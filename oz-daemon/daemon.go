package daemon

import (
	"fmt"
	"os"
	"os/signal"
	"path"
	"strings"
	"syscall"

	"github.com/subgraph/oz"
	"github.com/subgraph/oz/ipc"
	"github.com/subgraph/oz/network"

	"github.com/op/go-logging"
)

type daemonState struct {
	log         *logging.Logger
	config      *oz.Config
	profiles    oz.Profiles
	sandboxes   []*Sandbox
	nextSboxId  int
	nextDisplay int
	memBackend  *logging.ChannelMemoryBackend
	backends    []logging.Backend
	network     *network.HostNetwork
}

func Main() {
	d := initialize()

	err := runServer(
		d.log,
		d.handlePing,
		d.handleListProfiles,
		d.handleLaunch,
		d.handleListSandboxes,
		d.handleKillSandbox,
		d.handleMountFiles,
		d.handleUnmountFile,
		d.handleLogs,
	)
	if err != nil {
		d.log.Error("Error running server: %v", err)
	}
}

func initialize() *daemonState {
	sigs := make(chan os.Signal)
	signal.Notify(sigs, syscall.SIGHUP, syscall.SIGUSR1)

	d := &daemonState{}
	d.initializeLogging()
	config, err := d.loadConfig()
	if err != nil {
		d.log.Error("Could not load configuration: %s", oz.DefaultConfigPath, err)
		os.Exit(1)
	}
	d.config = config
	ps, err := d.loadProfiles(d.config.ProfileDir)
	if err != nil {
		d.log.Fatalf("Failed to load profiles: %v", err)
		os.Exit(1)
	}
	d.profiles = ps
	oz.ReapChildProcs(d.log, d.handleChildExit)
	d.nextSboxId = 1
	d.nextDisplay = 100

	for _, pp := range d.profiles {
		if pp.Networking.Nettype == network.TYPE_BRIDGE {
			d.log.Info("Initializing bridge networking")
			htn, err := network.BridgeInit(d.config.BridgeMACAddr, d.config.NMIgnoreFile, d.log)
			if err != nil {
				d.log.Fatalf("Failed to initialize bridge networking: %+v", err)
				return nil
			}

			d.network = htn

			network.NetPrint(d.log)

			break
		}
	}

	sockets := path.Join(config.SandboxPath, "sockets")
	if err := os.MkdirAll(sockets, 0755); err != nil {
		d.log.Fatalf("Failed to create sockets directory: %v", err)
	}

	go d.processSignals(sigs)

	return d
}

func (d *daemonState) loadConfig() (*oz.Config, error) {
	config, err := oz.LoadConfig(oz.DefaultConfigPath)
	if err != nil {
		if os.IsNotExist(err) {
			d.log.Info("Configuration file (%s) is missing, using defaults.", oz.DefaultConfigPath)
			config = oz.NewDefaultConfig()
		} else {
			return nil, err
		}
	}
	d.log.Info("Oz Global Config: %+v", config)

	return config, nil
}

func (d *daemonState) loadProfiles(profileDir string) (oz.Profiles, error) {
	ps, err := oz.LoadProfiles(profileDir)
	if err != nil {
		return nil, err
	}
	d.Debug("%d profiles loaded", len(ps))
	return ps, nil
}

func (d *daemonState) processSignals(c <-chan os.Signal) {
	for {
		sig := <-c
		switch sig {
		case syscall.SIGHUP:
			d.log.Notice("Received HUP signal, reloading profiles.")

			ps, err := d.loadProfiles(d.config.ProfileDir)
			if err != nil {
				d.log.Error("Failed to reload profiles: %v", err)
				return
			}
			d.profiles = ps
		case syscall.SIGUSR1:
			d.handleNetworkReconfigure()
		}
	}
}

func (d *daemonState) handleChildExit(pid int, wstatus syscall.WaitStatus) {
	d.Debug("Child process pid=%d exited with status %d", pid, wstatus.ExitStatus())

	for _, sbox := range d.sandboxes {
		if sbox.init.Process.Pid == pid {
			sbox.remove(d.log)
			return
		}
	}
	d.Notice("No sandbox found with oz-init pid = %d", pid)
}

func runServer(log *logging.Logger, args ...interface{}) error {
	s, err := ipc.NewServer(SocketName, messageFactory, log, args...)
	if err != nil {
		return err
	}

	return s.Run()
}

func (d *daemonState) handlePing(msg *PingMsg, m *ipc.Message) error {
	d.Debug("received ping with data [%s]", msg.Data)
	return m.Respond(&PingMsg{msg.Data})
}

func (d *daemonState) handleListProfiles(msg *ListProfilesMsg, m *ipc.Message) error {
	r := new(ListProfilesResp)
	index := 1
	for _, p := range d.profiles {
		r.Profiles = append(r.Profiles, Profile{Index: index, Name: p.Name, Path: p.Path})
		index += 1
	}
	return m.Respond(r)
}

func (d *daemonState) handleLaunch(msg *LaunchMsg, m *ipc.Message) error {
	d.Debug("Launch message received. Path: %s Name: %s Pwd: %s Args: %+v", msg.Path, msg.Name, msg.Pwd, msg.Args)
	p, err := d.getProfileFromLaunchMsg(msg)
	if err != nil {
		return m.Respond(&ErrorMsg{err.Error()})
	}

	if sbox := d.getRunningSandboxByName(p.Name); sbox != nil {
		if msg.Noexec {
			errmsg := "Asked to launch program but sandbox is running and noexec is set!"
			d.Notice(errmsg)
			return m.Respond(&ErrorMsg{errmsg})
		} else {
			d.Info("Found running sandbox for `%s`, running program there", p.Name)
			sbox.launchProgram(d.config.PrefixPath, msg.Path, msg.Pwd, msg.Args, d.log)
		}
	} else {
		d.Debug("Would launch %s", p.Name)
		msg.Env = d.sanitizeEnvironment(p, msg.Env)
		_, err = d.launch(p, msg, m.Ucred.Uid, m.Ucred.Gid, d.log)
		if err != nil {
			d.Warning("Launch of %s failed: %v", p.Name, err)
			return m.Respond(&ErrorMsg{err.Error()})
		}
	}
	return m.Respond(&OkMsg{})
}

func (d *daemonState) sanitizeEnvironment(p *oz.Profile, oldEnv []string) []string {
	newEnv := []string{}

	for _, EnvItem := range d.config.EnvironmentVars {
		for _, OldItem := range oldEnv {
			if strings.HasPrefix(OldItem, EnvItem+"=") {
				newEnv = append(newEnv, EnvItem+"="+strings.Replace(OldItem, EnvItem+"=", "", 1))

				break
			}
		}
	}

	for _, EnvItem := range p.Environment {
		if EnvItem.Name == "" {
			continue
		}
		if EnvItem.Value != "" {
			d.log.Info("Setting environment variable: %s=%s\n", EnvItem.Name, EnvItem.Value)

			newEnv = append(newEnv, EnvItem.Name+"="+EnvItem.Value)
		} else {
			for _, OldItem := range oldEnv {
				if strings.HasPrefix(OldItem, EnvItem.Name+"=") {
					NewValue := strings.Replace(OldItem, EnvItem.Name+"=", "", 1)
					newEnv = append(newEnv, EnvItem.Name+"="+NewValue)

					d.log.Info("Cloning environment variable: %s=%s\n", EnvItem.Name, NewValue)

					break
				}
			}
		}
	}

	return newEnv
}

func (d *daemonState) handleKillSandbox(msg *KillSandboxMsg, m *ipc.Message) error {
	if msg.Id == -1 {
		for _, sb := range d.sandboxes {
			if err := sb.init.Process.Signal(os.Interrupt); err != nil {
				return m.Respond(&ErrorMsg{fmt.Sprintf("failed to send interrupt signal: %v", err)})
			}
		}
	} else {
		sbox := d.sandboxById(msg.Id)
		if sbox == nil {
			return m.Respond(&ErrorMsg{fmt.Sprintf("no sandbox found with id = %d", msg.Id)})
		}
		if err := sbox.init.Process.Signal(os.Interrupt); err != nil {
			return m.Respond(&ErrorMsg{fmt.Sprintf("failed to send interrupt signal: %v", err)})
		}
	}
	return m.Respond(&OkMsg{})
}

func (d *daemonState) handleMountFiles(msg *MountFilesMsg, m *ipc.Message) error {
	sbox := d.sandboxById(msg.Id)
	if sbox == nil {
		return m.Respond(&ErrorMsg{fmt.Sprintf("no sandbox found with id = %d", msg.Id)})
	}
	if err := sbox.MountFiles(msg.Files, msg.ReadOnly, d.config.PrefixPath, d.log); err != nil {
		return m.Respond(&ErrorMsg{fmt.Sprintf("Unable to unmount file `%+s` from sandbox `%s`: %v", msg.Files, sbox.profile.Name, err)})
	}
	return m.Respond(&OkMsg{})
}


func (d *daemonState) handleUnmountFile(msg *UnmountFileMsg, m *ipc.Message) error {
	sbox := d.sandboxById(msg.Id)
	if sbox == nil {
		return m.Respond(&ErrorMsg{fmt.Sprintf("no sandbox found with id = %d", msg.Id)})
	}
	if err := sbox.UnmountFile(msg.File, d.config.PrefixPath, d.log); err != nil {
		return m.Respond(&ErrorMsg{fmt.Sprintf("Unable to unmount file `%s` from sandbox `%s`: %v", msg.File, sbox.profile.Name, err)})
	}
	return m.Respond(&OkMsg{})
}



func (d *daemonState) sandboxById(id int) *Sandbox {
	for _, sb := range d.sandboxes {
		if sb.id == id {
			return sb
		}
	}
	return nil
}

func (d *daemonState) getProfileFromLaunchMsg(msg *LaunchMsg) (*oz.Profile, error) {
	if msg.Index == 0 && msg.Name == "" {
		return d.getProfileByPath(msg.Path)
	}
	return d.getProfileByIdxOrName(msg.Index, msg.Name)
}

func (d *daemonState) getProfileByPath(cpath string) (*oz.Profile, error) {
	for _, p := range d.profiles {
		if p.Path == cpath {
			return p, nil
		}
		for _, pp := range p.Paths {
			if pp == cpath {
				return p, nil
			}
		}
	}

	return nil, fmt.Errorf("could not find profile path '%s'", cpath)
}

func (d *daemonState) getProfileByIdxOrName(index int, name string) (*oz.Profile, error) {
	if len(name) == 0 {
		if index < 1 || index > len(d.profiles) {
			return nil, fmt.Errorf("not a valid profile index (%d)", index)
		}
		return d.profiles[index-1], nil
	}

	for _, p := range d.profiles {
		if p.Name == name {
			return p, nil
		}
	}
	return nil, fmt.Errorf("could not find profile name '%s'", name)
}

func (d *daemonState) getRunningSandboxByName(name string) *Sandbox {
	for _, sb := range d.sandboxes {
		if sb.profile.Name == name {
			return sb
		}
	}

	return nil
}

func (d *daemonState) handleListSandboxes(list *ListSandboxesMsg, msg *ipc.Message) error {
	r := new(ListSandboxesResp)
	for _, sb := range d.sandboxes {
		r.Sandboxes = append(r.Sandboxes, SandboxInfo{Id: sb.id, Address: sb.addr, Mounts: sb.mountedFiles, Profile: sb.profile.Name})
	}
	return msg.Respond(r)
}

func (d *daemonState) handleLogs(logs *LogsMsg, msg *ipc.Message) error {
	for n := d.memBackend.Head(); n != nil; n = n.Next() {
		s := n.Record.Formatted(0)
		msg.Respond(&LogData{Lines: []string{s}})
	}
	if logs.Follow {
		d.followLogs(msg)
		return nil
	}
	msg.Respond(&OkMsg{})
	return nil
}

func (d *daemonState) handleNetworkReconfigure() {
	brIP, brNet, err := network.FindEmptyRange()
	if err != nil {
		return
	}
	if brIP.Equal(d.network.Gateway) {
		d.log.Notice("Range is still available, not reconfiguring.")
		return
	}
	d.log.Notice("Network has changed, reconfiguring with %s %s", brIP.String(), brNet.String())

	if err := d.network.BridgeReconfigure(d.log); err != nil {
		d.log.Error("Unable to reconfigure bridge network: %v", err)
		return
	}
	/*
		for _, sbox := range d.sandboxes {
			if sbox.profile.Networking.Nettype == network.TYPE_BRIDGE {
				sbox.network, err := network.PrepareSandboxNetwork(d.network, d.log)
				if err != nil {
					d.log.Error("Unable to prepare reconfigure of sandbox `%s` networking: %v", sbox.profile.Name, err)
					continue
				}
				if err := d.network.NetReconfigure(d.network, sbox.network, sbox.Pid, d.log); err != nil {
					d.log.Error("Unable to reconfigure sandbox `%s` networking: %v", sbox.profile.Name, err)
					continue
				}
				// TODO: Reconfigure default gateway inside sandbox
			}
		}
	*/
	return
}
