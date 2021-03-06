// DO NOT EDIT. Autogenerated by syscalls_gen.go

package seccomp

// #include "unistd_64.h"
import "C"

// syscallNum maps system call names to numbers.
var syscallNum = map[string]int{
	"read":                   C.__NR_read,
	"write":                  C.__NR_write,
	"open":                   C.__NR_open,
	"close":                  C.__NR_close,
	"stat":                   C.__NR_stat,
	"fstat":                  C.__NR_fstat,
	"lstat":                  C.__NR_lstat,
	"poll":                   C.__NR_poll,
	"lseek":                  C.__NR_lseek,
	"mmap":                   C.__NR_mmap,
	"mprotect":               C.__NR_mprotect,
	"munmap":                 C.__NR_munmap,
	"brk":                    C.__NR_brk,
	"rt_sigaction":           C.__NR_rt_sigaction,
	"rt_sigprocmask":         C.__NR_rt_sigprocmask,
	"rt_sigreturn":           C.__NR_rt_sigreturn,
	"ioctl":                  C.__NR_ioctl,
	"pread64":                C.__NR_pread64,
	"pwrite64":               C.__NR_pwrite64,
	"readv":                  C.__NR_readv,
	"writev":                 C.__NR_writev,
	"access":                 C.__NR_access,
	"pipe":                   C.__NR_pipe,
	"select":                 C.__NR_select,
	"sched_yield":            C.__NR_sched_yield,
	"mremap":                 C.__NR_mremap,
	"msync":                  C.__NR_msync,
	"mincore":                C.__NR_mincore,
	"madvise":                C.__NR_madvise,
	"shmget":                 C.__NR_shmget,
	"shmat":                  C.__NR_shmat,
	"shmctl":                 C.__NR_shmctl,
	"dup":                    C.__NR_dup,
	"dup2":                   C.__NR_dup2,
	"pause":                  C.__NR_pause,
	"nanosleep":              C.__NR_nanosleep,
	"getitimer":              C.__NR_getitimer,
	"alarm":                  C.__NR_alarm,
	"setitimer":              C.__NR_setitimer,
	"getpid":                 C.__NR_getpid,
	"sendfile":               C.__NR_sendfile,
	"socket":                 C.__NR_socket,
	"connect":                C.__NR_connect,
	"accept":                 C.__NR_accept,
	"sendto":                 C.__NR_sendto,
	"recvfrom":               C.__NR_recvfrom,
	"sendmsg":                C.__NR_sendmsg,
	"recvmsg":                C.__NR_recvmsg,
	"shutdown":               C.__NR_shutdown,
	"bind":                   C.__NR_bind,
	"listen":                 C.__NR_listen,
	"getsockname":            C.__NR_getsockname,
	"getpeername":            C.__NR_getpeername,
	"socketpair":             C.__NR_socketpair,
	"setsockopt":             C.__NR_setsockopt,
	"getsockopt":             C.__NR_getsockopt,
	"clone":                  C.__NR_clone,
	"fork":                   C.__NR_fork,
	"vfork":                  C.__NR_vfork,
	"execve":                 C.__NR_execve,
	"exit":                   C.__NR_exit,
	"wait4":                  C.__NR_wait4,
	"kill":                   C.__NR_kill,
	"uname":                  C.__NR_uname,
	"semget":                 C.__NR_semget,
	"semop":                  C.__NR_semop,
	"semctl":                 C.__NR_semctl,
	"shmdt":                  C.__NR_shmdt,
	"msgget":                 C.__NR_msgget,
	"msgsnd":                 C.__NR_msgsnd,
	"msgrcv":                 C.__NR_msgrcv,
	"msgctl":                 C.__NR_msgctl,
	"fcntl":                  C.__NR_fcntl,
	"flock":                  C.__NR_flock,
	"fsync":                  C.__NR_fsync,
	"fdatasync":              C.__NR_fdatasync,
	"truncate":               C.__NR_truncate,
	"ftruncate":              C.__NR_ftruncate,
	"getdents":               C.__NR_getdents,
	"getcwd":                 C.__NR_getcwd,
	"chdir":                  C.__NR_chdir,
	"fchdir":                 C.__NR_fchdir,
	"rename":                 C.__NR_rename,
	"mkdir":                  C.__NR_mkdir,
	"rmdir":                  C.__NR_rmdir,
	"creat":                  C.__NR_creat,
	"link":                   C.__NR_link,
	"unlink":                 C.__NR_unlink,
	"symlink":                C.__NR_symlink,
	"readlink":               C.__NR_readlink,
	"chmod":                  C.__NR_chmod,
	"fchmod":                 C.__NR_fchmod,
	"chown":                  C.__NR_chown,
	"fchown":                 C.__NR_fchown,
	"lchown":                 C.__NR_lchown,
	"umask":                  C.__NR_umask,
	"gettimeofday":           C.__NR_gettimeofday,
	"getrlimit":              C.__NR_getrlimit,
	"getrusage":              C.__NR_getrusage,
	"sysinfo":                C.__NR_sysinfo,
	"times":                  C.__NR_times,
	"ptrace":                 C.__NR_ptrace,
	"getuid":                 C.__NR_getuid,
	"syslog":                 C.__NR_syslog,
	"getgid":                 C.__NR_getgid,
	"setuid":                 C.__NR_setuid,
	"setgid":                 C.__NR_setgid,
	"geteuid":                C.__NR_geteuid,
	"getegid":                C.__NR_getegid,
	"setpgid":                C.__NR_setpgid,
	"getppid":                C.__NR_getppid,
	"getpgrp":                C.__NR_getpgrp,
	"setsid":                 C.__NR_setsid,
	"setreuid":               C.__NR_setreuid,
	"setregid":               C.__NR_setregid,
	"getgroups":              C.__NR_getgroups,
	"setgroups":              C.__NR_setgroups,
	"setresuid":              C.__NR_setresuid,
	"getresuid":              C.__NR_getresuid,
	"setresgid":              C.__NR_setresgid,
	"getresgid":              C.__NR_getresgid,
	"getpgid":                C.__NR_getpgid,
	"setfsuid":               C.__NR_setfsuid,
	"setfsgid":               C.__NR_setfsgid,
	"getsid":                 C.__NR_getsid,
	"capget":                 C.__NR_capget,
	"capset":                 C.__NR_capset,
	"rt_sigpending":          C.__NR_rt_sigpending,
	"rt_sigtimedwait":        C.__NR_rt_sigtimedwait,
	"rt_sigqueueinfo":        C.__NR_rt_sigqueueinfo,
	"rt_sigsuspend":          C.__NR_rt_sigsuspend,
	"sigaltstack":            C.__NR_sigaltstack,
	"utime":                  C.__NR_utime,
	"mknod":                  C.__NR_mknod,
	"uselib":                 C.__NR_uselib,
	"personality":            C.__NR_personality,
	"ustat":                  C.__NR_ustat,
	"statfs":                 C.__NR_statfs,
	"fstatfs":                C.__NR_fstatfs,
	"sysfs":                  C.__NR_sysfs,
	"getpriority":            C.__NR_getpriority,
	"setpriority":            C.__NR_setpriority,
	"sched_setparam":         C.__NR_sched_setparam,
	"sched_getparam":         C.__NR_sched_getparam,
	"sched_setscheduler":     C.__NR_sched_setscheduler,
	"sched_getscheduler":     C.__NR_sched_getscheduler,
	"sched_get_priority_max": C.__NR_sched_get_priority_max,
	"sched_get_priority_min": C.__NR_sched_get_priority_min,
	"sched_rr_get_interval":  C.__NR_sched_rr_get_interval,
	"mlock":                  C.__NR_mlock,
	"munlock":                C.__NR_munlock,
	"mlockall":               C.__NR_mlockall,
	"munlockall":             C.__NR_munlockall,
	"vhangup":                C.__NR_vhangup,
	"modify_ldt":             C.__NR_modify_ldt,
	"pivot_root":             C.__NR_pivot_root,
	"_sysctl":                C.__NR__sysctl,
	"prctl":                  C.__NR_prctl,
	"arch_prctl":             C.__NR_arch_prctl,
	"adjtimex":               C.__NR_adjtimex,
	"setrlimit":              C.__NR_setrlimit,
	"chroot":                 C.__NR_chroot,
	"sync":                   C.__NR_sync,
	"acct":                   C.__NR_acct,
	"settimeofday":           C.__NR_settimeofday,
	"mount":                  C.__NR_mount,
	"umount2":                C.__NR_umount2,
	"swapon":                 C.__NR_swapon,
	"swapoff":                C.__NR_swapoff,
	"reboot":                 C.__NR_reboot,
	"sethostname":            C.__NR_sethostname,
	"setdomainname":          C.__NR_setdomainname,
	"iopl":                   C.__NR_iopl,
	"ioperm":                 C.__NR_ioperm,
	"create_module":          C.__NR_create_module,
	"init_module":            C.__NR_init_module,
	"delete_module":          C.__NR_delete_module,
	"get_kernel_syms":        C.__NR_get_kernel_syms,
	"query_module":           C.__NR_query_module,
	"quotactl":               C.__NR_quotactl,
	"nfsservctl":             C.__NR_nfsservctl,
	"getpmsg":                C.__NR_getpmsg,
	"putpmsg":                C.__NR_putpmsg,
	"afs_syscall":            C.__NR_afs_syscall,
	"tuxcall":                C.__NR_tuxcall,
	"security":               C.__NR_security,
	"gettid":                 C.__NR_gettid,
	"readahead":              C.__NR_readahead,
	"setxattr":               C.__NR_setxattr,
	"lsetxattr":              C.__NR_lsetxattr,
	"fsetxattr":              C.__NR_fsetxattr,
	"getxattr":               C.__NR_getxattr,
	"lgetxattr":              C.__NR_lgetxattr,
	"fgetxattr":              C.__NR_fgetxattr,
	"listxattr":              C.__NR_listxattr,
	"llistxattr":             C.__NR_llistxattr,
	"flistxattr":             C.__NR_flistxattr,
	"removexattr":            C.__NR_removexattr,
	"lremovexattr":           C.__NR_lremovexattr,
	"fremovexattr":           C.__NR_fremovexattr,
	"tkill":                  C.__NR_tkill,
	"time":                   C.__NR_time,
	"futex":                  C.__NR_futex,
	"sched_setaffinity":      C.__NR_sched_setaffinity,
	"sched_getaffinity":      C.__NR_sched_getaffinity,
	"set_thread_area":        C.__NR_set_thread_area,
	"io_setup":               C.__NR_io_setup,
	"io_destroy":             C.__NR_io_destroy,
	"io_getevents":           C.__NR_io_getevents,
	"io_submit":              C.__NR_io_submit,
	"io_cancel":              C.__NR_io_cancel,
	"get_thread_area":        C.__NR_get_thread_area,
	"lookup_dcookie":         C.__NR_lookup_dcookie,
	"epoll_create":           C.__NR_epoll_create,
	"epoll_ctl_old":          C.__NR_epoll_ctl_old,
	"epoll_wait_old":         C.__NR_epoll_wait_old,
	"remap_file_pages":       C.__NR_remap_file_pages,
	"getdents64":             C.__NR_getdents64,
	"set_tid_address":        C.__NR_set_tid_address,
	"restart_syscall":        C.__NR_restart_syscall,
	"semtimedop":             C.__NR_semtimedop,
	"fadvise64":              C.__NR_fadvise64,
	"timer_create":           C.__NR_timer_create,
	"timer_settime":          C.__NR_timer_settime,
	"timer_gettime":          C.__NR_timer_gettime,
	"timer_getoverrun":       C.__NR_timer_getoverrun,
	"timer_delete":           C.__NR_timer_delete,
	"clock_settime":          C.__NR_clock_settime,
	"clock_gettime":          C.__NR_clock_gettime,
	"clock_getres":           C.__NR_clock_getres,
	"clock_nanosleep":        C.__NR_clock_nanosleep,
	"exit_group":             C.__NR_exit_group,
	"epoll_wait":             C.__NR_epoll_wait,
	"epoll_ctl":              C.__NR_epoll_ctl,
	"tgkill":                 C.__NR_tgkill,
	"utimes":                 C.__NR_utimes,
	"vserver":                C.__NR_vserver,
	"mbind":                  C.__NR_mbind,
	"set_mempolicy":          C.__NR_set_mempolicy,
	"get_mempolicy":          C.__NR_get_mempolicy,
	"mq_open":                C.__NR_mq_open,
	"mq_unlink":              C.__NR_mq_unlink,
	"mq_timedsend":           C.__NR_mq_timedsend,
	"mq_timedreceive":        C.__NR_mq_timedreceive,
	"mq_notify":              C.__NR_mq_notify,
	"mq_getsetattr":          C.__NR_mq_getsetattr,
	"kexec_load":             C.__NR_kexec_load,
	"waitid":                 C.__NR_waitid,
	"add_key":                C.__NR_add_key,
	"request_key":            C.__NR_request_key,
	"keyctl":                 C.__NR_keyctl,
	"ioprio_set":             C.__NR_ioprio_set,
	"ioprio_get":             C.__NR_ioprio_get,
	"inotify_init":           C.__NR_inotify_init,
	"inotify_add_watch":      C.__NR_inotify_add_watch,
	"inotify_rm_watch":       C.__NR_inotify_rm_watch,
	"migrate_pages":          C.__NR_migrate_pages,
	"openat":                 C.__NR_openat,
	"mkdirat":                C.__NR_mkdirat,
	"mknodat":                C.__NR_mknodat,
	"fchownat":               C.__NR_fchownat,
	"futimesat":              C.__NR_futimesat,
	"newfstatat":             C.__NR_newfstatat,
	"unlinkat":               C.__NR_unlinkat,
	"renameat":               C.__NR_renameat,
	"linkat":                 C.__NR_linkat,
	"symlinkat":              C.__NR_symlinkat,
	"readlinkat":             C.__NR_readlinkat,
	"fchmodat":               C.__NR_fchmodat,
	"faccessat":              C.__NR_faccessat,
	"pselect6":               C.__NR_pselect6,
	"ppoll":                  C.__NR_ppoll,
	"unshare":                C.__NR_unshare,
	"set_robust_list":        C.__NR_set_robust_list,
	"get_robust_list":        C.__NR_get_robust_list,
	"splice":                 C.__NR_splice,
	"tee":                    C.__NR_tee,
	"sync_file_range":        C.__NR_sync_file_range,
	"vmsplice":               C.__NR_vmsplice,
	"move_pages":             C.__NR_move_pages,
	"utimensat":              C.__NR_utimensat,
	"epoll_pwait":            C.__NR_epoll_pwait,
	"signalfd":               C.__NR_signalfd,
	"timerfd_create":         C.__NR_timerfd_create,
	"eventfd":                C.__NR_eventfd,
	"fallocate":              C.__NR_fallocate,
	"timerfd_settime":        C.__NR_timerfd_settime,
	"timerfd_gettime":        C.__NR_timerfd_gettime,
	"accept4":                C.__NR_accept4,
	"signalfd4":              C.__NR_signalfd4,
	"eventfd2":               C.__NR_eventfd2,
	"epoll_create1":          C.__NR_epoll_create1,
	"dup3":                   C.__NR_dup3,
	"pipe2":                  C.__NR_pipe2,
	"inotify_init1":          C.__NR_inotify_init1,
	"preadv":                 C.__NR_preadv,
	"pwritev":                C.__NR_pwritev,
	"rt_tgsigqueueinfo":      C.__NR_rt_tgsigqueueinfo,
	"perf_event_open":        C.__NR_perf_event_open,
	"recvmmsg":               C.__NR_recvmmsg,
	"fanotify_init":          C.__NR_fanotify_init,
	"fanotify_mark":          C.__NR_fanotify_mark,
	"prlimit64":              C.__NR_prlimit64,
	"name_to_handle_at":      C.__NR_name_to_handle_at,
	"open_by_handle_at":      C.__NR_open_by_handle_at,
	"clock_adjtime":          C.__NR_clock_adjtime,
	"syncfs":                 C.__NR_syncfs,
	"sendmmsg":               C.__NR_sendmmsg,
	"setns":                  C.__NR_setns,
	"getcpu":                 C.__NR_getcpu,
	"process_vm_readv":       C.__NR_process_vm_readv,
	"process_vm_writev":      C.__NR_process_vm_writev,
	"kcmp":                   C.__NR_kcmp,
	"finit_module":           C.__NR_finit_module,
	"sched_setattr":          C.__NR_sched_setattr,
	"sched_getattr":          C.__NR_sched_getattr,
	"renameat2":              C.__NR_renameat2,
	"seccomp":                C.__NR_seccomp,
	"getrandom":              C.__NR_getrandom,
	"memfd_create":           C.__NR_memfd_create,
	"kexec_file_load":        C.__NR_kexec_file_load,
	"bpf":                    C.__NR_bpf,
	"execveat":               C.__NR_execveat,
}
