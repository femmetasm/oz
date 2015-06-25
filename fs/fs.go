package fs

import (
	"fmt"
	"os"
	"path"
	"strings"
	"syscall"

	"github.com/op/go-logging"
	"github.com/subgraph/oz"
	"os/user"
	"path/filepath"
)

type Filesystem struct {
	log    *logging.Logger
	base   string
	chroot bool
}

func NewFilesystem(config *oz.Config, log *logging.Logger) *Filesystem {
	if log == nil {
		log = logging.MustGetLogger("oz")
	}
	return &Filesystem{
		base: config.SandboxPath,
		log:  log,
	}
}

func (fs *Filesystem) Root() string {
	return path.Join(fs.base, "rootfs")
}

func (fs *Filesystem) CreateEmptyDir(target string) error {
	fi, err := os.Stat(target)
	if err != nil {
		return err
	}
	if !fs.chroot {
		target = path.Join(fs.Root(), target)
	}
	if err := os.MkdirAll(target, fi.Mode().Perm()); err != nil {
		return err
	}
	return copyFileInfo(fi, target)
}

func (fs *Filesystem) CreateDevice(devpath string, dev int, mode, perm uint32) error {
	p := path.Join(fs.Root(), devpath)
	if err := syscall.Mknod(p, mode, dev); err != nil {
		return fmt.Errorf("failed to mknod device '%s': %v", p, err)
	}
	if err := os.Chmod(p, os.FileMode(perm)); err != nil {
		return fmt.Errorf("unable to set file permissions on device '%s': %v", p, err)
	}
	return nil
}

func (fs *Filesystem) CreateSymlink(oldpath, newpath string) error {
	if !fs.chroot {
		newpath = path.Join(fs.Root(), newpath)
	}
	if err := syscall.Symlink(oldpath, newpath); err != nil {
		return fmt.Errorf("failed to symlink %s to %s: %v", newpath, oldpath, err)
	}
	return nil
}

func (fs *Filesystem) BindPath(path, target string, readonly bool) error {
	return fs.BindOrCreate(path, target, readonly, nil)
}

func (fs *Filesystem) BindOrCreate(p, target string, readonly bool, u *user.User) error {
	src, err := filepath.EvalSymlinks(p)
	if err != nil {
		return fmt.Errorf("error resolving symlinks for path (%s): %v", p, err)
	}
	sinfo, err := readSourceInfo(src, u)
	if err != nil {
		return fmt.Errorf("failed to bind path (%s): %v", src, err)
	}

	target = path.Join(fs.Root(), target)

	_, err = os.Stat(target)
	if err == nil || !os.IsNotExist(err) {
		fs.log.Warning("Target (%s > %s) already exists, ignoring", src, target)
		return nil
	}

	if sinfo.IsDir() {
		if err := os.MkdirAll(target, sinfo.Mode().Perm()); err != nil {
			return err
		}
	} else {
		if err := createEmptyFile(target, 0750); err != nil {
			return err
		}
	}

	if err := copyPathPermissions(fs.Root(), src); err != nil {
		return fmt.Errorf("failed to copy path permissions for (%s): %v", src, err)
	}
	fs.log.Info("bind mounting %s -> %s", src, target)
	flags := syscall.MS_NOSUID | syscall.MS_NODEV
	if readonly {
		flags |= syscall.MS_RDONLY
	} else {
		flags |= syscall.MS_NOEXEC
	}
	return bindMount(src, target, flags)
}

func readSourceInfo(src string, u *user.User) (os.FileInfo, error) {
	if fi, err := os.Stat(src); err == nil {
		return fi, nil
	} else if !os.IsNotExist(err) {
		return nil, err
	}

	if u == nil {
		return nil, fmt.Errorf("source path (%s) does not exist", src)
	}

	home := u.HomeDir
	if !strings.HasPrefix(src, home) {
		return nil, fmt.Errorf("mount item (%s) has flag MountCreateIfAbsent, but is not child of home directory (%s)", src, home)
	}

	if err := os.MkdirAll(src, 0750); err != nil {
		return nil, err
	}

	pinfo, err := os.Stat(path.Dir(src))
	if err != nil {
		return nil, err
	}

	if err := copyFileInfo(pinfo, src); err != nil {
		return nil, err
	}

	return os.Stat(src)
}

func (fs *Filesystem) BlacklistPath(target string) error {
	t, err := filepath.EvalSymlinks(target)
	if err != nil {
		return fmt.Errorf("symlink evaluation failed while blacklisting path %s: %v", target, err)
	}
	fi, err := os.Stat(t)
	if err != nil {
		if os.IsNotExist(err) {
			fs.log.Info("Blacklist path (%s) does not exist", t)
			return nil
		}
		return err
	}
	src := emptyFilePath
	if fi.IsDir() {
		src = emptyDirPath
	}
	if !fs.chroot {
		src = path.Join(fs.Root(), src)
		t = path.Join(fs.Root(), t)
	}
	if err := syscall.Mount(src, t, "", syscall.MS_BIND, "mode=400,gid=0"); err != nil {
		return fmt.Errorf("failed to bind %s -> %s for blacklist: %v", src, t, err)
	}
	return nil
}

func (fs *Filesystem) Chroot() error {
	if fs.chroot {
		return fmt.Errorf("filesystem is already in chroot()")
	}
	fs.log.Debug("chroot to %s", fs.Root())
	if err := syscall.Chroot(fs.Root()); err != nil {
		return fmt.Errorf("chroot to %s failed: %v", fs.Root(), err)
	}
	if err := os.Chdir("/"); err != nil {
		return fmt.Errorf("chdir to / after chroot() failed: %v", err)
	}
	fs.chroot = true
	return nil
}

func (fs *Filesystem) MountProc() error {
	err := fs.mountSpecial("/proc", "proc", 0, "")
	if err != nil {
		return err
	}
	roMounts := []string{
		"sysrq-trigger",
		"bus",
		"irq",
		"sys/kernel/hotplug",
	}
	for _, rom := range roMounts {
		if _, err := os.Stat(rom); err == nil {
			if err := bindMount(rom, rom, syscall.MS_RDONLY); err != nil {
				return fmt.Errorf("remount RO of %s failed: %v", rom, err)
			}
		}
	}
	return nil
}

func (fs *Filesystem) MountFullDev() error {
	return fs.mountSpecial("/dev", "devtmpfs", 0, "")
}

func (fs *Filesystem) MountSys() error {
	return fs.mountSpecial("/sys", "sysfs", syscall.MS_RDONLY, "")
}

func (fs *Filesystem) MountTmp() error {
	return fs.mountSpecial("/tmp", "tmpfs", syscall.MS_NODEV, "")
}

func (fs *Filesystem) MountPts() error {
	return fs.mountSpecial("/dev/pts", "devpts", 0, "newinstance,ptmxmode=0666")
}

func (fs *Filesystem) MountShm() error {
	return fs.mountSpecial("/dev/shm", "tmpfs", syscall.MS_NODEV, "")
}

func (fs *Filesystem) mountSpecial(path, mtype string, flags int, args string) error {
	if !fs.chroot {
		return fmt.Errorf("cannot mount %s (%s) until Chroot() is called.", path, mtype)
	}
	fs.log.Debug("Mounting %s [%s]", path, mtype)
	if err := os.MkdirAll(path, 0755); err != nil {
		return fmt.Errorf("failed to create mount point (%s): %v", path, err)
	}
	mountFlags := uintptr(flags | syscall.MS_NOSUID | syscall.MS_NOEXEC | syscall.MS_REC)
	return syscall.Mount("", path, mtype, mountFlags, args)
}

func bindMount(source, target string, flags int) error {
	if err := syscall.Mount(source, target, "", syscall.MS_BIND, ""); err != nil {
		return fmt.Errorf("bind mount of %s -> %s failed: %v", source, target, err)
	}
	if flags != 0 {
		return remount(target, flags)
	}
	return nil
}

func remount(target string, flags int) error {
	fl := uintptr(flags | syscall.MS_BIND | syscall.MS_REMOUNT)
	if err := syscall.Mount("", target, "", fl, ""); err != nil {
		return fmt.Errorf("failed to remount %s with flags %x: %v", target, flags, err)
	}
	return nil
}

const emptyFilePath = "/oz.ro.file"
const emptyDirPath = "/oz.ro.dir"

func (fs *Filesystem) CreateBlacklistPaths() error {
	p := emptyDirPath
	if !fs.chroot {
		p = path.Join(fs.Root(), emptyDirPath)
	}
	if err := createBlacklistDir(p); err != nil {
		return err
	}
	p = emptyFilePath
	if !fs.chroot {
		p = path.Join(fs.Root(), emptyFilePath)
	}
	if err := createBlacklistFile(p); err != nil {
		return err
	}
	return nil
}

func createBlacklistDir(p string) error {
	if err := os.MkdirAll(p, 0000); err != nil {
		return err
	}
	return setBlacklistPerms(p, 0500)
}

func createBlacklistFile(path string) error {
	fd, err := os.Create(path)
	if err != nil {
		return err
	}
	if err := fd.Close(); err != nil {
		return err
	}
	return setBlacklistPerms(path, 0400)
}

func setBlacklistPerms(path string, mode os.FileMode) error {
	if err := os.Chown(path, 0, 0); err != nil {
		return err
	}
	if err := os.Chmod(path, mode); err != nil {
		return err
	}
	return nil
}

func createEmptyFile(name string, mode os.FileMode) error {
	if err := os.MkdirAll(path.Dir(name), 0750); err != nil {
		return err
	}
	fd, err := os.Create(name)
	if err != nil {
		return err
	}
	if err := fd.Close(); err != nil {
		return err
	}
	if err := os.Chmod(name, mode); err != nil {
		return err
	}
	return nil
}

func copyPathPermissions(root, src string) error {
	current := "/"
	for _, part := range strings.Split(src, "/") {
		if part == "" {
			continue
		}
		current = path.Join(current, part)
		target := path.Join(root, current)
		if err := copyFilePermissions(current, target); err != nil {
			return err
		}
	}
	return nil
}

func copyFilePermissions(src, target string) error {
	fi, err := os.Stat(src)
	if err != nil {
		return err
	}
	return copyFileInfo(fi, target)
}

func copyFileInfo(info os.FileInfo, target string) error {
	st := info.Sys().(*syscall.Stat_t)
	os.Chown(target, int(st.Uid), int(st.Gid))
	os.Chmod(target, info.Mode().Perm())
	return nil
}
