/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Mkfs Tool.                           */
/*                                                                        */
/*    Copyright (C) 2016-2018 TrustInSoft                                 */
/*                                                                        */
/*  TrustInSoft Mkfs Tool is released under GPLv2                         */
/*                                                                        */
/**************************************************************************/

#include <sys/socket.h>
#include <sys/mman.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

#include <tis_builtin.h>
//@ assigns *__fc_stdout \from format[..];
int tis_printf(const char *__restrict format, ...);

#include <__tis_mkfs.h>

//==============================================================================
/* This macro can be used to get un unknown assertion on non implemented
 * features when it is ok to continue. If it is incorrect to continue,
 * it is better to use \false. */
extern volatile char tis_mkfs_unknown;
#define WARN_NIY (tis_mkfs_unknown == 0)

#ifdef __TIS_MKFS_NO_ERR
#define RETURN_RANDOM_ERROR(r)
#else
#define RETURN_RANDOM_ERROR(r) { \
  if (tis_nondet (0, 1)) { \
    tis_make_unknown(&errno, sizeof errno); \
    return r; \
  } \
}
#endif // __TIS_MKFS_NO_ERR
//==============================================================================
#ifdef __TIS_MKFS_STATIC_ALLOCATE
#define __TIS_MKFS_STD_ALLOCATE
#elif defined __TIS_MKFS_PREALLOCATE
// the value of this variable must be provided externally
extern size_t __tis_mkfs_preallocate_size;
static unsigned char * alloc_data (int ino, size_t st_size) {
  //@ assert file_fits_1: st_size <= __tis_mkfs_preallocate_size ;
  return malloc (__tis_mkfs_preallocate_size);
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  //@ assert file_fits_2: st_size <= __tis_mkfs_preallocate_size ;
  return old;
}
#elif defined __TIS_MKFS_DYNAMIC_ALLOCATE
static size_t __max(size_t a, size_t b) {
  return (a>b)?a:b;
}
static unsigned char * alloc_data (int ino, size_t st_size) {
  return malloc (__max (1, st_size));
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  return realloc (old, __max (1, st_size));
}
#else
#define __TIS_MKFS_STD_ALLOCATE
#endif

#ifdef __TIS_MKFS_STD_ALLOCATE
// standard allocation mode: static array.
#define TIS_FSIZE INT_MAX
unsigned char __fc_data_table[FOPEN_MAX][TIS_FSIZE];
static const size_t __tis_mkfs_allocate_size = TIS_FSIZE;
static unsigned char * alloc_data (int ino, size_t st_size) {
  //@ assert file_fits_1: st_size <= __tis_mkfs_allocate_size ;
  return __fc_data_table + ino;
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  //@ assert file_fits_2: st_size <= __tis_mkfs_allocate_size ;
  return old;
}
#endif

//==============================================================================

// No need to dynamically allocate inodes.
// There are already statically allocated for pre-existing objects.
// This table is a pool of inodes to be used for new objects.
static int __tis_mkfs_next_inode_table = 0;
static struct stat __tis_mkfs_inode_table[FOPEN_MAX];
static const size_t __tis_mkfs_inode_nb_max = FOPEN_MAX;

struct __tis_fd_info __tis_file_desc[FOPEN_MAX];
struct __tis_socket __tis_fd_socket[FOPEN_MAX];

//==============================================================================

struct stat * __tis_mk_inode (int mode) {
  struct stat * st =
    __tis_mkfs_next_inode_table < __tis_mkfs_inode_nb_max ?
    __tis_mkfs_inode_table + __tis_mkfs_next_inode_table++
    : NULL;
  //@ assert no_more_inode_mkfs_niy: st != \null;
  st->st_ino = __tis_next_inode++;
  st->st_mode = mode;
  st->st_uid = __tis_uid;
  st->st_gid = __tis_gid;
  st->st_size = 0;
  st->st_nlink = 1;
  st->st_dev = __TIS_MKFS_ST_DEV;
  st->st_blksize = __TIS_MKFS_BLKSIZE;
  return st;
}

void __tis_init_fd_file (FILE * f, int fd, int kind, int flags,
    struct stat * st, struct __fc_fs_file * file) {
  __tis_file_desc [fd].__tis_fd_kind = kind;
  f->__fc_stdio_id = fd;
  f->__fc_position.__fc_stdio_position = 0;
  f->__fc_error = 0;
  f->__fc_eof = 0;
  f->__fc_flags = flags;
  f->__fc_inode = st;
  f->__fc_file = file;
}

struct __fc_fs_file __fc_fs_stdin, __fc_fs_stdout, __fc_fs_stderr;

struct stat __tis_stdin_inode = {
  .st_mode = S_IFCHR | S_IRUSR | S_IRGRP | S_IROTH,
  .st_nlink = 1,
  .st_dev = __TIS_MKFS_ST_DEV,
  .st_blksize = __TIS_MKFS_BLKSIZE,
};

struct stat __tis_stdout_inode = {
  .st_mode = S_IFCHR | S_IWUSR | S_IWGRP | S_IWOTH,
  .st_nlink = 1,
  .st_dev = __TIS_MKFS_ST_DEV,
  .st_blksize = __TIS_MKFS_BLKSIZE,
};

struct stat __tis_stderr_inode = {
  .st_mode = S_IFCHR | S_IWUSR | S_IWGRP | S_IWOTH,
  .st_nlink = 1,
  .st_dev = __TIS_MKFS_ST_DEV,
  .st_blksize = __TIS_MKFS_BLKSIZE,
};

/*@
// when this property is not valid, it is probably that the source file
// generated by tis-mkfs has not been provided to the analyzer.
requires mkfs_next_inode_definition:
0 <= __tis_next_inode && __tis_next_inode < INT_MAX; */
__attribute__((constructor))
  void __tis_mkfs_init_stdio (void) {
    __tis_stdin_inode.st_ino = __tis_next_inode ++;
    __tis_stdin_inode.st_uid = __tis_uid;
    __tis_stdin_inode.st_gid = __tis_gid;
    __tis_init_fd_file (stdin, 0, S_IFCHR, O_RDONLY, &__tis_stdin_inode,
        &__fc_fs_stdin);
    __fc_fopen[0] = *stdin;

    __tis_stdout_inode.st_ino = __tis_next_inode ++;
    __tis_stdout_inode.st_uid = __tis_uid;
    __tis_stdout_inode.st_gid = __tis_gid;
    __tis_init_fd_file (stdout, 1, S_IFCHR, O_WRONLY, &__tis_stdout_inode,
        &__fc_fs_stdout);
    __fc_fopen[1] = *stdout;

    __tis_stderr_inode.st_ino = __tis_next_inode ++;
    __tis_stderr_inode.st_uid = __tis_uid;
    __tis_stderr_inode.st_gid = __tis_gid;
    __tis_init_fd_file (stderr, 2, S_IFCHR, O_WRONLY, &__tis_stderr_inode,
        &__fc_fs_stderr);
    __fc_fopen[2] = *stderr;
  }

// set errno when \result == -1;
int __tis_get_next_file_desc (void) {
#ifndef __TIS_MKFS_NO_CLOSE
  /*@ slevel 1025; */
  for (int i = 0; i < FOPEN_MAX; i++) {
    if (__tis_file_desc[i].__tis_fd_kind == 0)
      return i;
  }
  /*@ slevel default; */
#else // __TIS_MKFS_NO_CLOSE
  static int __tis_next_fd = 3;
  if (__tis_next_fd < FOPEN_MAX)
    return __tis_next_fd++;
#endif // __TIS_MKFS_NO_CLOSE

  RETURN_RANDOM_ERROR (-1);

  errno = EMFILE;
  return -1;
}

// set errno when \result == -1;
int __tis_check_fd_ok (int fd) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}
// set errno when \result == -1;
int __tis_check_fd_file_ok (int fd) {
  int res = __tis_check_fd_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res == -1)
    return -1;
  if (__tis_file_desc [fd].__tis_fd_kind == S_IFDIR) {
    errno = EISDIR;
    return -1;
  }
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFREG
      && __tis_file_desc [fd].__tis_fd_kind != S_IFIFO
      && __tis_file_desc [fd].__tis_fd_kind != S_IFCHR) {
    errno = EBADF;
    return -1;
  }
  if (__fc_fopen[fd].__fc_stdio_id != fd || __fc_fopen[fd].__fc_inode == NULL) {
    errno = EBADF;
    return -1;
  }
  return 0;
}
// set errno when \result == -1;
int __tis_check_fd_dir_ok (int fd) {
  int res = __tis_check_fd_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res == -1)
    return -1;
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFDIR) {
    errno = EBADF;
    return -1;
  }
  if ( __fc_opendir[fd].__fc_dir_id != fd
      || __fc_opendir[fd].__fc_dir_inode == NULL) {
    errno = EBADF;
    return -1;
  }
  return 0;
}
// set errno when \result == -1;
int __tis_check_fd_socket_ok (int fd) {
  int res = __tis_check_fd_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res == -1)
    return -1;
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFSOCK) {
    errno = EBADF;
    return -1;
  }
  if (__tis_fd_socket[fd].__tis_sock_id != fd) {
    errno = EBADF;
    return -1;
  }
  return 0;
}

//==============================================================================
// About files : stdio.h, unistd.h and sys/stat.h functions.
//==============================================================================
// Getting information: 'stat' and 'getxxx' functions
//------------------------------------------------------------------------------
// set errno when \result == -1;
/*@ requires tis_access_mode:
  (mode & (__tis_R_OK | __tis_W_OK | __tis_X_OK)) == mode;
  */
int __tis_stat_access (struct stat * st, int mode) {
  mode_t m = st->st_mode;
  int ok;
  if (st->st_uid == __tis_euid) {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IRUSR) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWUSR) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXUSR) : ok;
  }
  else if (st->st_uid == __tis_egid) {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IRGRP) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWGRP) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXGRP) : ok;
  }
  else {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IROTH) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWOTH) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXOTH) : ok;
  }
  if (ok) {
    RETURN_RANDOM_ERROR (-1);
    return 0;
  }
  else {
    errno = EBADF;
    return -1;
  }
}
// set errno when \result == -1;
int __tis_check_fd_file_ok_for_reading (int fd) {
  int ret = __tis_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __tis_check_fd_file_ok
    return -1;
  if (__fc_fopen[fd].__fc_flags & O_WRONLY) {
    errno = EBADF;
    return -1;
  }
  ret = __tis_stat_access (__fc_fopen[fd].__fc_inode, R_OK);
  return ret;
}

// set errno when \result == -1;
int __tis_check_fd_file_ok_for_writing (int fd) {
  int ret = __tis_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __tis_check_fd_file_ok
    return -1;
  if (!(__fc_fopen[fd].__fc_flags & O_WRONLY) &&
      !(__fc_fopen[fd].__fc_flags & O_RDWR)) {
    errno = EBADF;
    return -1;
  }
  ret = __tis_stat_access (__fc_fopen[fd].__fc_inode, W_OK);
  return ret;
}

// set errno when \result == -1;
int __tis_mkfs_fstat(int fd, struct stat *buf) {
  int ret = __tis_check_fd_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __tis_check_fd_file_ok
    return -1;
  struct stat * st;
  if (__tis_file_desc [fd].__tis_fd_kind == S_IFREG
      || __tis_file_desc [fd].__tis_fd_kind == S_IFIFO)
    st = __fc_fopen[fd].__fc_inode;
  else if (__tis_file_desc [fd].__tis_fd_kind == S_IFDIR)
    st = __fc_opendir[fd].__fc_dir_inode;
  else {
    errno = EBADF;
    return -1;
  }
  *buf = *st;
  return 0;
}
#ifndef __TIS_USER_FSTAT
int fstat(int fd, struct stat *buf)
{ return __tis_mkfs_fstat(fd, buf); }
#endif // __TIS_USER_FSTAT

// set errno when \result == -1;
int __tis_mkfs_stat(const char *pathname, struct stat *buf) {
  int f = __tis_mkfs_get_file (pathname);
  if (f != -1) {
    RETURN_RANDOM_ERROR (-1);
    *buf = *(__fc_fs_files[f].__fc_stat);
    return 0;
  }
  int d = __tis_mkfs_get_dir (pathname);
  if (d != -1) {
    RETURN_RANDOM_ERROR (-1);
    *(buf) = *( __fc_fs_dirs[d].__fc_stat);
    return 0;
  }
  RETURN_RANDOM_ERROR (-1);
  errno = ENOENT;
  return -1;
}
#ifndef __TIS_USER_STAT
int stat(const char *pathname, struct stat *buf)
{ return __tis_mkfs_stat(pathname, buf); }
#endif //__TIS_USER_STAT

int __tis_mkfs_lstat(const char *pathname, struct stat *buf) {
  int ret = stat (pathname, buf);
  if (0 == ret) {
    if (S_ISLNK (buf->st_mode)) {
      //@ assert lstat_links_mkfs_niy: WARN_NIY ;
      return -1;
    }
    return ret;
  }
  return ret;
}
#ifndef __TIS_USER_LSTAT
int lstat(const char *pathname, struct stat *buf)
{ return __tis_mkfs_lstat(pathname, buf); }
#endif // __TIS_USER_LSTAT

// set errno when \result == -1;
int __tis_mkfs_access(const char *pathname, int mode) {
  struct stat buf_stat;
  if (mode != F_OK && (mode & (R_OK | W_OK | X_OK) != mode)) {
    errno = EINVAL;
    return -1;
  }
  if (0 == stat (pathname, &buf_stat)) { // know element: test mode
    if (mode == F_OK) return 0;
    return __tis_stat_access (&buf_stat, mode); // handle __TIS_MKFS_NO_ERR
  }
  else { // unknown file or directory
    tis_make_unknown ((char*)&errno, sizeof (errno));
    return -1;
  }
}
#ifndef __TIS_USER_ACCESS
int access(const char *pathname, int mode)
{ return __tis_mkfs_access(pathname, mode); }
#endif // __TIS_USER_ACCESS

// set errno when \result == -1;
int __tis_mkfs_fileno(FILE *stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  return fd;
}
#ifndef __TIS_USER_FILENO
// set errno when \result == -1;
int fileno(FILE *stream)
{ return __tis_mkfs_fileno(stream); }
#endif // __TIS_USER_FILENO

// always valid (no errno)
int __tis_mkfs_feof(FILE *stream) {
  return stream->__fc_eof;
}
#ifndef __TIS_USER_FEOF
// always valid (no errno)
int feof(FILE *stream)
{ return __tis_mkfs_feof(stream); }
#endif // __TIS_USER_FEOF

// always valid (no errno)
int __tis_mkfs_ferror(FILE *stream) {
  return stream->__fc_error;
}
#ifndef __TIS_USER_FERROR
// always valid (no errno)
int ferror(FILE *stream)
{ return __tis_mkfs_ferror(stream); }
#endif // __TIS_USER_FERROR

// always valid (no errno)
void __tis_mkfs_clearerr(FILE *stream) {
  stream->__fc_eof = 0;
  stream->__fc_error = 0;
}
#ifndef __TIS_USER_CLEARERR
// always valid (no errno)
void clearerr(FILE *stream)
{ __tis_mkfs_clearerr(stream); }
#endif // __TIS_USER_CLEARERR

uid_t __tis_mkfs_getuid(void) { return __tis_uid; }
#ifndef __TIS_USER_GETUID
uid_t getuid(void) { return __tis_mkfs_getuid(); }
#endif // __TIS_USER_GETUID

uid_t __tis_mkfs_geteuid(void) { return __tis_euid; }
#ifndef __TIS_USER_GETEUID
uid_t geteuid(void) { return __tis_mkfs_geteuid(); }
#endif // __TIS_USER_GETEUID

uid_t __tis_mkfs_getgid(void) { return __tis_gid; }
#ifndef __TIS_USER_GETGID
uid_t getgid(void) { return __tis_mkfs_getgid(); }
#endif // __TIS_USER_GETGID

uid_t __tis_mkfs_getegid(void) { return __tis_egid; }
#ifndef __TIS_USER_GETEGID
uid_t getegid(void) { return __tis_mkfs_getegid(); }
#endif // __TIS_USER_GETEGID

//==============================================================================
// 'open' file functions
//------------------------------------------------------------------------------
// everything is checked already : just do it.
// set errno when \result == -1;
int __tis_open_fd (int fd, int kind, int flags, unsigned char * content,
    struct stat * st, struct __fc_fs_file * file) {
  __tis_file_desc[fd].__tis_fd_kind = kind;
  FILE * stream = __fc_fopen + fd;
  __tis_init_fd_file (stream, fd, kind, flags, st, file);

  if ((flags & O_TRUNC) && ((flags & O_WRONLY) || (flags & O_RDWR))) {
    st->st_size = 0;
  }

  if (!file->__fc_data) {
    unsigned char * ptr = NULL;
    if (content || flags & O_CREAT) {
      ino_t ino = st->st_ino;
      ptr = alloc_data (ino, st->st_size);
      if (ptr == NULL) {
        errno = ENOMEM;
        return -1;
      }
      if (st->st_size > 0)
        memcpy (ptr, content, st->st_size);
    }
    file->__fc_data = ptr;
  }
  return 0;
}

// set errno when \result == -1;
int __tis_create_file (const char * filename, int mode) {
  if (__fc_fs_files_nb >= __fc_fs_files_nb_max) {
    // use -nb-max-created-files to increase the maximum.
    errno = EMFILE;
    return -1;
  }

  //@ assert register_new_file_in_dirent_niy: WARN_NIY ;

  RETURN_RANDOM_ERROR (-1);

  char * filename2 = strdup (filename);
#ifdef __TIS_MKFS_NO_ERR
  //@ assert tis_mkfs_fopen_strdup_ok: filename2 != \null;
#endif

  struct stat * st = __tis_mk_inode (S_IFREG | mode);
  int f = __fc_fs_files_nb;
  __fc_fs_files_nb++;
  __fc_fs_files [f].__fc_fullpath = filename2;
  __fc_fs_files [f].__fc_stat = st;
  __fc_fs_files [f].__fc_content = NULL;
  return f;
}

// set errno when \result == -1;
/*@ requires tis_open_flags: ((flags & __tis_O_RDONLY) == __tis_O_RDONLY)
  || ((flags & __tis_O_WRONLY) == __tis_O_WRONLY)
  || ((flags & __tis_O_RDWR) == __tis_O_RDWR);
  */
int __tis_open_file (const char * filename, int flags, int mode) {
  int f = __tis_mkfs_get_file (filename);
  struct __fc_fs_file * file;
  if (flags & O_CREAT) {
    if (f == -1) {
      f = __tis_create_file (filename, mode); // handle __TIS_MKFS_NO_ERR
      if (f == -1)
        return -1; // errno already set __tis_create_file
    }
    else if (flags & O_EXCL) {
      errno = EEXIST;
      return -1;
    }
  }
  if (f != -1) {
    file = __fc_fs_files + f;
    struct stat * st = file->__fc_stat;
    if ((flags & O_RDONLY) || (flags & O_RDWR)) {
      if (-1 == __tis_stat_access (st, R_OK)) // handle __TIS_MKFS_NO_ERR
        // errno already set in __tis_stat_access
        return -1;
    }
    if ((flags & O_WRONLY) || (flags & O_RDWR)) {
      if (-1 == __tis_stat_access (st, W_OK)) // handle __TIS_MKFS_NO_ERR
        // errno already set in __tis_stat_access
        return -1;
    }
    int fd = __tis_get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
    if (fd != -1) {
      char * content = file->__fc_content ? (file->__fc_content ()) : NULL;
      int res = __tis_open_fd (fd, S_IFREG, flags, content, st, file);
      if (res != 0)
        return res;
    }
    // else errno already set in __tis_get_next_file_desc
    return fd;
  }
  errno = ENOENT;
  return -1;
}
int __tis_translate_mode_string (const char * restrict mode) {
  char c1 = mode[0];
  char * c = mode + 1;
  char cb = 0, cp = 0, ce = 0, cc = 0, cm = 0, cx = 0;
  if (*c == 'b') { cb = 1; c++; }
  if (*c == '+') {
    cp = 1; c++;
    if (! cb && *c == 'b') {
      cb = 1; c++;
      if (*c == '+') {
        cp = 1; c++;
      }
    }
  }
#ifdef _GNU_SOURCE
  if (*c == 'c') { cc = 1; c++; }
  if (*c == 'e') { ce = 1; c++; }
  if (*c == 'm') { cm = 1; c++; }
#endif
#if defined (_GNU_SOURCE) || ((__STDC_VERSION - 0) >= 201112L)
  if (*c == 'x') { cx = 1; c++; }
#endif
  if (*c != 0) {
    errno = EINVAL;
    return -1;
  }
  int flags;
  if (c1 == 'r') {
    flags = cp ? O_RDWR : O_RDONLY;
  }
  else if (c1 == 'w') {
    flags = cp ? O_RDWR | O_CREAT | O_TRUNC : O_WRONLY | O_CREAT | O_TRUNC;
  }
  else if (c1 == 'a') {
    flags = cp ? O_RDWR | O_CREAT | O_APPEND : O_WRONLY | O_CREAT | O_APPEND;
  }
  else {
    // terminating the analysis here since an out-of-spec mode string
    // is UB in C99
    //@ assert mkfs_open_mode_string_out_of_spec: \false;
    return -1;
  }
#ifdef _GNU_SOURCE
  if (cc) /*@ assert fopen_glibc_ext_c_niy: WARN_NIY; */ ;
  if (ce) flags |= O_CLOEXEC;
  if (cm) /*@ assert fopen_glibc_ext_m_niy: WARN_NIY; */ ;
#endif
#if defined (_GNU_SOURCE) || ((__STDC_VERSION - 0) >= 201112L)
  if (cx) flags |= O_EXCL;
#endif
  return flags;
}
int __tis_mkfs_open(const char * filename, int flags, va_list va) {
  int mode;
  if (flags & __tis_O_CREAT) {
    mode = va_arg(va, int);
  } else {
    mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;
  }
  return __tis_open_file (filename, flags, mode); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_OPEN
int open(const char * filename, int flags, ...) {
  va_list va;
  va_start(va, flags);
  int rv = __tis_mkfs_open(filename, flags, va);
  va_end(va);
  return rv;
}
#endif // __TIS_USER_OPEN

int __tis_mkfs_creat(const char *filename, mode_t mode) {
  int flags = O_WRONLY|O_CREAT|O_TRUNC;
  return __tis_open_file (filename, flags, mode); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_CREAT
int creat(const char *filename, mode_t mode) {
  return __tis_mkfs_creat (filename, mode);
}
#endif // __TIS_USER_CREAT

FILE* __tis_mkfs_fdopen(int fd, const char * restrict mode) {
  int ret = __tis_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __tis_check_fd_file_ok
    return NULL;
  int flags = __tis_translate_mode_string (mode);
  if (flags == -1)
    // errno already set by __tis_translate_mode_string (EINVAL)
    return NULL;
  if (__fc_fopen[fd].__fc_flags != flags) {
    errno = EINVAL;
    return NULL;
  }
  return &__fc_fopen[fd];
}
#ifndef __TIS_USER_FDOPEN
FILE* fdopen(int fd, const char * restrict mode)
{ return __tis_mkfs_fdopen(fd, mode); }
#endif // __TIS_USER_FDOPEN

FILE* __tis_mkfs_fopen(const char * restrict filename,
    const char * restrict open_mode) {
  int flags = __tis_translate_mode_string (open_mode);
  if (flags == -1)
    // errno already set by __tis_translate_mode_string (EINVAL)
    return NULL;
  int mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;
  int fd = __tis_open_file (filename, flags, mode); // handle __TIS_MKFS_NO_ERR
  if (fd == -1)
    // errno already set by __tis_open_file
    return NULL;

  return &__fc_fopen[fd];
}
#ifndef __TIS_USER_FOPEN
FILE* fopen(const char * restrict filename,
    const char * restrict open_mode)
{ return __tis_mkfs_fopen(filename, open_mode); }
#endif // __TIS_USER_FOPEN

// #ifndef __TIS_USER_FREOPEN
// FILE *freopen(const char *path, const char *mode, FILE *stream) {
// TODO
// }
// #endif // __TIS_USER_FREOPEN

// set errno when \result == -1;
int __tis_mkfs_dup2(int oldfd, int newfd) {
  if (__tis_check_fd_ok(oldfd) == -1)
    return -1;
  if (__tis_file_desc[oldfd].__tis_fd_kind == 0) {
    errno = EBADF;
    return -1;
  }
  if (__tis_check_fd_ok(newfd) == -1)
    return -1;
  if (newfd == oldfd)
    return newfd;
  if (__tis_file_desc[newfd].__tis_fd_kind != 0)
    close(newfd);
  __tis_file_desc[newfd].__tis_fd_kind = __tis_file_desc[oldfd].__tis_fd_kind;

  // TODO: copying information is not correct. It should be a link.
  // See comment in [__tis_fd_info] definition to see how to fix it.
  switch (__tis_file_desc[oldfd].__tis_fd_kind) {
    case S_IFCHR:
    case S_IFIFO:
    case S_IFREG:
      __fc_fopen[newfd] = __fc_fopen[oldfd];
    case S_IFDIR:
      __fc_opendir[newfd] = __fc_opendir[oldfd];
    case S_IFSOCK:
      __tis_fd_socket[newfd] = __tis_fd_socket[oldfd];
  }
  return newfd;
}
#ifndef __TIS_USER_DUP2
int dup2(int oldfd, int newfd)
{ return __tis_mkfs_dup2(oldfd, newfd); }
#endif // __TIS_USER_DUP2

int __tis_mkfs_dup(int oldfd) {
  return dup2(oldfd, __tis_get_next_file_desc());
}
#ifndef __TIS_USER_DUP
int dup(int oldfd)
{ return __tis_mkfs_dup(oldfd); }
#endif // __TIS_USER_DUP

//==============================================================================
/*
 * TODO: implement error checking:
 * 1. setvbuf must be called before any I/O operation on the stream
 * 2. the application loses ownership of the buffer following this
 * call (and gets it back when the stream is closed? this isn't clear
 * from the spec)
 */
// set errno when \result == -1;
int __tis_mkfs_setvbuf(FILE *stream, char *buf, int mode, size_t size) {
  if (mode != _IONBF && mode != _IOLBF && mode != _IOFBF) {
    tis_make_unknown ((char*)&errno, sizeof (errno));
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);

  stream->__fc_flags |= mode;
  return 0;
}
#ifndef __TIS_USER_SETVBUF
// set errno when \result == -1;
int setvbuf(FILE *stream, char *buf, int mode, size_t size)
{ return __tis_mkfs_setvbuf(stream, buf, mode, size); }
#endif // __TIS_USER_SETVBUF

void __tis_mkfs_setbuf(FILE *stream, char *buf) {
  setvbuf(stream, buf, buf ? _IOFBF : _IONBF, BUFSIZ);
}
#ifndef __TIS_USER_SETBUF
void setbuf(FILE *stream, char *buf)
{ __tis_mkfs_setbuf(stream, buf); }
#endif // __TIS_USER_SETBUF

void __tis_mkfs_setbuffer(FILE *stream, char *buf, size_t size) {
  setvbuf(stream, buf, buf ? _IOFBF : _IONBF, size);
}
#ifndef __TIS_USER_SETBUFFER
void setbuffer(FILE *stream, char *buf, size_t size)
{ __tis_mkfs_setbuffer(stream, buf, size); }
#endif // __TIS_USER_SETBUFFER

void __tis_mkfs_setlinebuf(FILE *stream) {
  setvbuf(stream, NULL, _IOLBF, 0);
}
#ifndef __TIS_USER_SETLINEBUF
void setlinebuf(FILE *stream)
{ __tis_mkfs_setlinebuf(stream); }
#endif // __TIS_USER_SETLINEBUF

int __tis_mkfs_fflush(FILE *stream) {
  RETURN_RANDOM_ERROR (-1);
  // TODO: model errors -- this function has UBs that we could look for
  // N.B. no need to actually flush here since we don't do buffering
  return 0;
}
#ifndef __TIS_USER_FFLUSH
int fflush(FILE *stream)
{ return __tis_mkfs_fflush(stream); }
#endif // __TIS_USER_FFLUSH

//==============================================================================
// 'read' file functions
//------------------------------------------------------------------------------
ssize_t __tis_pread (int fd, void *buf, size_t count, off_t offset) {
  if (offset < 0) {
    errno = EINVAL;
    return -1;
  }
  int ret = __tis_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) {
    return ret;
  }
  FILE * stream = __fc_fopen + fd;
  struct stat * st = stream->__fc_inode;
  size_t max = st->st_size;
  if (offset >= max)
    return 0;
  size_t n_avail = max - offset;
  size_t n_read = (n_avail >= count) ? count : n_avail;
  unsigned char * data = stream->__fc_file->__fc_data;
  if (data)
    memcpy (buf, data + offset, n_read);
  else
    tis_make_unknown ((char*)buf, n_read);
  return n_read;
}

ssize_t __tis_read_file(int fd, void *buf, size_t count) {
  FILE * stream = &__fc_fopen[fd];
  unsigned long pos = stream->__fc_position.__fc_stdio_position;
  ssize_t n_read = __tis_pread (fd, buf, count, pos); // handle __TIS_MKFS_NO_ERR
  if (n_read > 0 && __tis_file_desc [fd].__tis_fd_kind == S_IFREG) {
    stream->__fc_position.__fc_stdio_position += n_read;
  }
  return n_read;
}
ssize_t __tis_read_socket(int fd, void *buf, size_t count) {
  ssize_t res = tis_long_long_interval(-1, count);
  if (res == -1) {
#ifdef __TIS_MKFS_NO_ERR
    res = 0;
#else
    tis_make_unknown((char*)&errno, sizeof(errno));
#endif
    return res;
  }
  tis_make_unknown(buf, res);
  return res;
}
ssize_t __tis_mkfs_read(int fd, void *buf, size_t count) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  switch (__tis_file_desc[fd].__tis_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: return __tis_read_file(fd, buf, count);
    case S_IFDIR: errno = EISDIR; return -1;
    case S_IFSOCK: return __tis_read_socket(fd, buf, count);
    default: tis_make_unknown ((char*)&errno, sizeof (errno));
             return -1;
  }
}
#ifndef __TIS_USER_READ
ssize_t read(int fd, void *buf, size_t count)
{ return __tis_mkfs_read(fd, buf, count); }
#endif // __TIS_USER_READ

size_t __tis_mkfs_fread(void * restrict ptr, size_t size,
    size_t nmemb, FILE * restrict stream) {
  size_t toread = size * nmemb;
  if (toread == 0)
    return 0;

  int fd = stream->__fc_stdio_id;
  int old_errno = errno;
  int n_bytes = -1;
  switch (__tis_file_desc[fd].__tis_fd_kind) {
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: n_bytes = __tis_read_file(fd, ptr, toread); break;
    case S_IFSOCK: n_bytes = __tis_read_socket(fd, ptr, toread); break;
  }
  if (n_bytes == -1) {
    errno = old_errno; // reset errno to its old value
    stream->__fc_error = tis_interval (1, CHAR_MAX);
    return 0;
  }
  if (n_bytes < toread)
#ifndef __TIS_MKFS_NO_ERR
    stream->__fc_eof = tis_interval (1, CHAR_MAX);
#else // to make tis-interpreter able to deal with EOF.
  stream->__fc_eof = 1;
#endif
  return n_bytes / size;
}
#ifndef __TIS_USER_FREAD
size_t fread(void * restrict ptr, size_t size, size_t nmemb,
    FILE * restrict stream)
{ return __tis_mkfs_fread(ptr, size, nmemb, stream); }
#endif // __TIS_USER_FREAD

ssize_t __tis_mkfs_pread(int fd, void *buf, size_t count, off_t offset) {
  return __tis_pread (fd, buf, count, offset); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PREAD
ssize_t pread(int fd, void *buf, size_t count, off_t offset)
{ return __tis_mkfs_pread(fd, buf, count, offset); }
#endif // __TIS_USER_PREAD

//------------------------------------------------------------------------------
// 'get' functions
//------------------------------------------------------------------------------

int __tis_mkfs_fgetc(FILE *stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) {
    stream->__fc_error = 1;
    return EOF;
  }
  unsigned int pos = stream->__fc_position.__fc_stdio_position;
  unsigned int max = stream->__fc_inode->st_size;
  if (pos >= max) {
    stream->__fc_eof = tis_interval (1, CHAR_MAX);
    return EOF;
  }
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFCHR)
    stream->__fc_position.__fc_stdio_position = pos + 1;
  unsigned char *data = stream->__fc_file->__fc_data;

  unsigned char c;
  if (data) {
    c = data[pos];
  }
  else {
    RETURN_RANDOM_ERROR (EOF);
    tis_make_unknown (&c, sizeof c);
  }
  return (int)c;
}
#ifndef __TIS_USER_FGETC
int fgetc(FILE *stream)
{ return __tis_mkfs_fgetc(stream); }
#endif // __TIS_USER_FGETC

int __tis_mkfs_getc(FILE *stream) {
  return fgetc (stream); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_GETC
int getc(FILE *stream)
{ return __tis_mkfs_getc(stream); }
#endif // __TIS_USER_GETC

int __tis_mkfs_ungetc(int c, FILE *stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  unsigned char *data = stream->__fc_file->__fc_data;
  if (data) {
    int pos = stream->__fc_position.__fc_stdio_position - 1;
    data[pos] = (unsigned char)c;
    if (__tis_file_desc [fd].__tis_fd_kind != S_IFCHR)
      stream->__fc_position.__fc_stdio_position = pos;
  }
  stream->__fc_eof = 0;
  RETURN_RANDOM_ERROR (EOF);
  return c;
}
#ifndef __TIS_USER_UNGETC
int ungetc(int c, FILE *stream)
{ return __tis_mkfs_ungetc(c, stream); }
#endif // __TIS_USER_UNGETC

int __tis_mkfs_getchar(void) {
  return getc (stdin); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_GETCHAR
int getchar(void)
{ return __tis_mkfs_getchar(); }
#endif // __TIS_USER_GETCHAR

char *__tis_mkfs_fgets(char * restrict s, int size, FILE * restrict stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) {
    return NULL;
  }
  if (size < 0) return NULL;
  if (stream->__fc_file->__fc_data) {
    int n = size - 1;
    unsigned int pos = stream->__fc_position.__fc_stdio_position;
    unsigned int max = stream->__fc_inode->st_size;
    if (pos >= max) return NULL;
    unsigned char *src = stream->__fc_file->__fc_data + pos;
    char *dst = s;
    while (n > 0 && pos < max) {
      if (*src == '\n') n = 1;
      *dst++ = *src++;
      n--;
      pos++;
    }
    *dst = 0;
    if (__tis_file_desc [fd].__tis_fd_kind != S_IFCHR)
      stream->__fc_position.__fc_stdio_position = pos;
  }
  else {
    int n = tis_interval (0, size - 1);
    tis_make_unknown (s, n);
    s[n] = 0;
  }
  return s;
}
#ifndef __TIS_USER_FGETS
char *fgets(char * restrict s, int size, FILE * restrict stream)
{ return __tis_mkfs_fgets(s, size, stream); }
#endif // __TIS_USER_FGETS

char *__tis_mkfs_gets(char *s) {
  int c = getchar (); // handle __TIS_MKFS_NO_ERR
  if (c == EOF)
    return NULL;
  int i;
  for (i = 0; (c != '\n' && c != EOF) ; i++, c = getchar ()) {
    s[i] = c;
  }
  s[i] = 0;
  return s;
}
#ifndef __TIS_USER_GETS
char *gets(char *s)
{ return __tis_mkfs_gets(s); }
#endif // __TIS_USER_GETS

//==============================================================================
// 'write' file functions
//------------------------------------------------------------------------------

/* to be used each time __fc_data[..] needs to be modified:
   in __tis_pwrite, __tis_mkfs_fputc, __tis_mkfs_fputs, ...
   Only handle __fc_data content. Depending on the case,
   the caller may also have to update the position and st_size.
   */
static int write__fc_data (FILE *stream, off_t offset,
    const void *buf, size_t count) {
  if (stream->__fc_file->__fc_data) {
    if (offset + count > stream->__fc_inode->st_size) {
      unsigned char * ptr;
      ptr = realloc_data (stream->__fc_file->__fc_data, offset + count);
#ifndef __TIS_MKFS_NO_ERR
      if (ptr == NULL) {
        tis_make_unknown ((char*)&errno, sizeof (errno));
        return -1;
      }
#else
      //@ assert write_no_err_realloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
      stream->__fc_file->__fc_data = ptr;
    }
    memcpy (stream->__fc_file->__fc_data + offset, buf, count);
  }
  else if (stream->__fc_file == &__fc_fs_stdout) {
    if (count <= (size_t)INT_MAX)
      tis_printf ("%.*s", (int)count, (const char *)buf);
  }
  return count;
}


// set errno when \result == -1;
ssize_t __tis_pwrite (int fd, const void *buf, size_t count, off_t offset) {
  if (offset < 0) {
    errno = EINVAL;
    return -1;
  }
  int ret = __tis_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  FILE * stream = __fc_fopen + fd;
  if (count == 0)
    return 0;
  if (stream->__fc_flags & O_APPEND)
    offset = stream->__fc_inode->st_size;

  ret = write__fc_data (stream, offset, buf, count);
  if (ret == -1)
    return -1;
  //@ assert mkfs__tis_pwrite_ok: ret == count;
  if (stream->__fc_file->__fc_data) {
    // if this write leaves a hole, fill it with zeros
    if (offset > stream->__fc_inode->st_size)
      memset (stream->__fc_file->__fc_data + stream->__fc_inode->st_size,
          0, offset - stream->__fc_inode->st_size);
  }
  if (offset + count > stream->__fc_inode->st_size)
    stream->__fc_inode->st_size = offset + count;
  return count;
}
ssize_t __tis_write_file(int fd, const void *buf, size_t count) {
  FILE * stream = &__fc_fopen[fd];
  unsigned long pos = stream->__fc_position.__fc_stdio_position;
  ssize_t n_write =
    __tis_pwrite (fd, buf, count, pos); // handle __TIS_MKFS_NO_ERR
  if (n_write > 0 && __tis_file_desc [fd].__tis_fd_kind != S_IFCHR) {
    if (stream->__fc_flags & O_APPEND)
      stream->__fc_position.__fc_stdio_position = stream->__fc_inode->st_size;
    else
      stream->__fc_position.__fc_stdio_position += n_write;
  }
  return n_write;
}
ssize_t __tis_write_socket(int fd, const void *buf, size_t count) {
  ssize_t res = tis_long_long_interval(-1, count);
#ifdef __TIS_MKFS_NO_ERR
  if (res == -1) res = 0;
#else
  if (res == -1) tis_make_unknown(&errno, sizeof errno);
#endif
  return res;
}
ssize_t __tis_mkfs_write(int fd, const void *buf, size_t count) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  switch (__tis_file_desc[fd].__tis_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: return __tis_write_file(fd, buf, count);
    case S_IFDIR: errno = EISDIR; return -1;
    case S_IFSOCK: return __tis_write_socket(fd, buf, count);
    default: tis_make_unknown(&errno, sizeof errno);
             return -1;
  }
}
#ifndef __TIS_USER_WRITE
ssize_t write(int fd, const void *buf, size_t count)
{ return __tis_mkfs_write(fd, buf, count); }
#endif // __TIS_USER_WRITE

size_t __tis_mkfs_fwrite(const void *ptr, size_t size, size_t nmemb,
    FILE *stream) {
  size_t towrite = size * nmemb;
  if (towrite == 0)
    return 0;

  int fd = stream->__fc_stdio_id;
  int old_errno = errno;
  size_t n_bytes = -1;
  switch (__tis_file_desc[fd].__tis_fd_kind) {
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: n_bytes = __tis_write_file(fd, ptr, towrite); break;
    case S_IFSOCK: n_bytes = __tis_write_socket(fd, ptr, towrite); break;
  }
  if (n_bytes == -1) {
    errno = old_errno; // reset errno to its old value
    stream->__fc_error = tis_interval (1, CHAR_MAX);
    return 0;
  }
  return n_bytes / size;
}
#ifndef __TIS_USER_FWRITE
size_t fwrite(const void *ptr, size_t size, size_t nmemb,
    FILE *stream)
{ return __tis_mkfs_fwrite(ptr, size, nmemb, stream); }
#endif // __TIS_USER_FWRITE

ssize_t __tis_mkfs_pwrite(int fd, const void *buf, size_t count, off_t offset) {
  // __fc_position is not changed on purpose (see man)
  return __tis_pwrite (fd, buf, count, offset); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PWRITE
ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset)
{ return __tis_mkfs_pwrite(fd, buf, count, offset); }
#endif // __TIS_USER_PWRITE

//------------------------------------------------------------------------------
// 'put' functions
//------------------------------------------------------------------------------

// set errno when \result == -1;
int __tis_mkfs_fputc(int c, FILE *stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  unsigned char uc = (unsigned char)c;
  unsigned int pos = stream->__fc_position.__fc_stdio_position;
  ret = write__fc_data (stream, pos, &c, 1);
  if (ret == -1)
    return ret;
  if (pos >= stream->__fc_inode->st_size) {
    stream->__fc_inode->st_size = pos+1;
  }
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFCHR)
    stream->__fc_position.__fc_stdio_position ++;
  return (int)(uc);
}
#ifndef __TIS_USER_FPUTC
int fputc(int c, FILE *stream)
{ return __tis_mkfs_fputc(c, stream); }
#endif // __TIS_USER_FPUTC

int __tis_mkfs_putc(int c, FILE *stream) {
  return fputc (c, stream); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PUTC
int putc(int c, FILE *stream)
{ return __tis_mkfs_putc(c, stream); }
#endif // __TIS_USER_PUTC

int __tis_mkfs_putchar(int c) {
  return putc (c, stdout); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PUTCHAR
int putchar(int c)
{ return __tis_mkfs_putchar(c); }
#endif // __TIS_USER_PUTCHAR

// set errno when \result == -1;
int __tis_mkfs_fputs(const char *s, FILE *stream) {
  int fd = stream->__fc_stdio_id;
  int ret = __tis_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  unsigned int pos = stream->__fc_position.__fc_stdio_position;
  int n = strlen (s);
  n = write__fc_data (stream, pos, s, n);
  if (n == -1)
    return n;
  if (pos + n > stream->__fc_inode->st_size)
    stream->__fc_inode->st_size = pos + n;
  if (__tis_file_desc [fd].__tis_fd_kind != S_IFCHR)
    stream->__fc_position.__fc_stdio_position = pos;
  return n;
}
#ifndef __TIS_USER_FPUTS
int fputs(const char *s, FILE *stream)
{ return __tis_mkfs_fputs(s, stream); }
#endif // __TIS_USER_FPUTS

int __tis_mkfs_puts(const char *s) {
  int n = fputs (s, stdout); // handle __TIS_MKFS_NO_ERR
  if (n != EOF) {
    n = putchar ('\n') != EOF ? n+1 : EOF;
  }
  return n;
}
#ifndef __TIS_USER_PUTS
int puts(const char *s)
{ return __tis_mkfs_puts(s); }
#endif // __TIS_USER_PUTS

//==============================================================================
// Offset functions (about fd position)
//------------------------------------------------------------------------------

int __tis_seekable (int fd) {
  if (fd < 0 || fd >= FOPEN_MAX
      || __tis_file_desc[fd].__tis_fd_kind != S_IFREG) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}

off_t __tis_mkfs_lseek(int fd, off_t offset, int whence) {
  if (__tis_seekable (fd) == -1) // handle __TIS_MKFS_NO_ERR
    return (off_t)(-1);

  FILE * stream = __fc_fopen + fd;
  off_t new_off;
  switch (whence) {
    case SEEK_SET:
      new_off = offset;
      break;
    case SEEK_END:
      new_off = stream->__fc_inode->st_size + offset;
      break;
    case SEEK_CUR:
      new_off = stream->__fc_position.__fc_stdio_position + offset;
      break;
    default:
      errno = EINVAL;
      return (off_t)(-1);
  }
  if (new_off < 0) {
    errno = EINVAL;
    return (off_t)(-1);
  }
  stream->__fc_position.__fc_stdio_position = new_off;
  return new_off;
}
#ifndef __TIS_USER_LSEEK
off_t lseek(int fd, off_t offset, int whence)
{ return __tis_mkfs_lseek(fd, offset, whence); }
#endif // __TIS_USER_LSEEK

int __tis_mkfs_fseek(FILE *stream, long offset, int whence) {
  off_t pos =
    lseek (stream->__fc_stdio_id, offset, whence); // handle __TIS_MKFS_NO_ERR
  if (pos == (off_t)(-1))
    return -1;
  else {
    stream->__fc_eof = 0;
    return 0;
  }
}
#ifndef __TIS_USER_FSEEK
int fseek(FILE *stream, long offset, int whence)
{ return __tis_mkfs_fseek(stream, offset, whence); }
#endif // __TIS_USER_FSEEK

long __tis_mkfs_ftell(FILE *stream) {
  if (__tis_seekable (stream->__fc_stdio_id) == -1) // handle __TIS_MKFS_NO_ERR
    return -1;
  return stream->__fc_position.__fc_stdio_position;
}
#ifndef __TIS_USER_FTELL
long ftell(FILE *stream)
{ return __tis_mkfs_ftell(stream); }
#endif // __TIS_USER_FTELL

void __tis_mkfs_rewind(FILE *stream) {
  (void) fseek (stream, 0L, SEEK_SET);
  clearerr (stream);
}
#ifndef __TIS_USER_REWIND
void rewind(FILE *stream)
{ __tis_mkfs_rewind(stream); }
#endif // __TIS_USER_REWIND

int __tis_mkfs_fgetpos(FILE *stream, fpos_t *pos) {
  if (__tis_seekable (stream->__fc_stdio_id) == -1) // handle __TIS_MKFS_NO_ERR
    return -1;
  *pos = stream->__fc_position;
  return 0;
}
#ifndef __TIS_USER_FGETPOS
int fgetpos(FILE *stream, fpos_t *pos)
{ return __tis_mkfs_fgetpos(stream, pos); }
#endif // __TIS_USER_FGETPOS

int __tis_mkfs_fsetpos(FILE *stream, const fpos_t *pos) {
  if (__tis_seekable (stream->__fc_stdio_id) == -1) // handle __TIS_MKFS_NO_ERR
    return -1;
  stream->__fc_position = *pos;
  return 0;
}
#ifndef __TIS_USER_FSETPOS
int fsetpos(FILE *stream, const fpos_t *pos)
{ return __tis_mkfs_fsetpos(stream, pos); }
#endif // __TIS_USER_FSETPOS

//==============================================================================
// 'truncate' functions
//------------------------------------------------------------------------------

// set errno when \result == -1;
int __tis_truncate (FILE * stream, off_t length) {
  struct stat * st = stream->__fc_inode;
  int ret = __tis_stat_access (st, W_OK); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  if (length < 0) {
    errno = EINVAL;
    return -1;
  }
  if (stream->__fc_file->__fc_data) {
    unsigned char * ptr;
    ptr = realloc_data (stream->__fc_file->__fc_data, length);
#ifndef __TIS_MKFS_NO_ERR
    if (ptr == NULL) {
      tis_make_unknown(&errno, sizeof errno);
      return -1;
    }
#else
    //@ assert truncate_no_err_realloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
    if (length > st->st_size)
      memset (ptr + st->st_size, 0, length - st->st_size);
    stream->__fc_file->__fc_data = ptr;
  }
  st->st_size = length;
  return 0;
}

// set errno when \result == -1;
int __tis_mkfs_ftruncate(int fd, off_t length) {
  int ret = __tis_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  ret = __tis_truncate (__fc_fopen + fd, length);
  return ret;
}
#ifndef __TIS_USER_FTRUNCATE
int ftruncate(int fd, off_t length)
{ return __tis_mkfs_ftruncate(fd, length); }
#endif // __TIS_USER_FTRUNCATE

// set errno when \result == -1;
int __tis_mkfs_truncate(const char *filename, off_t length) {
  int f = __tis_mkfs_get_file (filename);
  if (f != -1) {
    struct __fc_fs_file * file = __fc_fs_files + f;
    struct stat * st = file->__fc_stat;
    int ret = __tis_stat_access (st, W_OK); // handle __TIS_MKFS_NO_ERR
    if (ret != 0)
      return ret;

    st->st_size = length;
    file->__fc_content = NULL;
    return 0;
  }
  errno = ENOENT;
  return -1;
}
#ifndef __TIS_USER_TRUNCATE
int truncate(const char *filename, off_t length)
{ return __tis_mkfs_truncate(filename, length); }
#endif // __TIS_USER_TRUNCATE

// set errno when \result == -1;
int __tis_mkfs_fclose(FILE * restrict fp) {
  int fd = fp->__fc_stdio_id;
  int res = __tis_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res == -1)
    return -1;
  __tis_file_desc[fd].__tis_fd_kind = 0;
  __fc_fopen[fd].__fc_inode = NULL;
  return 0;
}
#ifndef __TIS_USER_FCLOSE
int fclose(FILE * restrict fp)
{ return __tis_mkfs_fclose(fp); }
#endif // __TIS_USER_FCLOSE

//==============================================================================
// About directories : dirent.h functions.
//==============================================================================

// set errno when \result == -1;
int __tis_opendir_fd (const char * pathname) {
  int d = __tis_mkfs_get_dir (pathname);
  if (d != -1) {
    struct __fc_fs_dir * dir = __fc_fs_dirs + d;
    struct stat * st = dir->__fc_stat;
    if (-1 == __tis_stat_access (st, R_OK)) // handle __TIS_MKFS_NO_ERR
      // errno already set in __tis_stat_access (EACCES)
      return -1;
    int fd = __tis_get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
    if (fd != -1) {
      __tis_file_desc[fd].__tis_fd_kind = S_IFDIR;
      __fc_opendir[fd].__fc_dir_id = fd;
      __fc_opendir[fd].__fc_dir_position = 0;
      __fc_opendir[fd].__fc_dir_inode = st;
      __fc_opendir[fd].__fc_dir_entries = dir->__fc_dir_entries;
    }
    // else errno already set in __tis_get_next_file_desc (ENFILE)
    return fd;
  }
  tis_make_unknown(&errno, sizeof errno);
  return -1;
}

// set errno when \result == NULL;
DIR * __tis_mkfs_fdopendir (int fd) {
  if (fd < 0 || fd >= FOPEN_MAX
      || __tis_file_desc[fd].__tis_fd_kind != S_IFDIR
      || __fc_opendir[fd].__fc_dir_inode == NULL
     ) {
    errno = EBADF;
    return NULL;
  }
  RETURN_RANDOM_ERROR (NULL);
  return &__fc_opendir[fd];
}
#ifndef __TIS_USER_FDOPENDIR
DIR * fdopendir (int fd)
{ return __tis_mkfs_fdopendir(fd); }
#endif // __TIS_USER_FDOPENDIR

// set errno when \result == NULL;
DIR *__tis_mkfs_opendir(const char * restrict path) {
  int fd = __tis_opendir_fd (path); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    return &__fc_opendir[fd];
  }
  return NULL;

}
#ifndef __TIS_USER_OPENDIR
DIR *opendir(const char * restrict path)
{ return __tis_mkfs_opendir(path); }
#endif // __TIS_USER_OPENDIR

int __tis_mkfs_dirfd(DIR *dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __tis_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return res;
  return fd;
}
#ifndef __TIS_USER_DIRFD
int dirfd(DIR *dirp)
{ return __tis_mkfs_dirfd(dirp); }
#endif // __TIS_USER_DIRFD

long __tis_mkfs_telldir(DIR *dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __tis_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return res;
  return dirp->__fc_dir_position;
}
#ifndef __TIS_USER_TELLDIR
long telldir(DIR *dirp)
{ return __tis_mkfs_telldir(dirp); }
#endif // __TIS_USER_TELLDIR

void __tis_mkfs_rewinddir (DIR *dirp) {
  // no error detection (no returned value)
  dirp->__fc_dir_position = 0;
}
#ifndef __TIS_USER_REWINDDIR
void rewinddir (DIR *dirp)
{ __tis_mkfs_rewinddir(dirp); }
#endif // __TIS_USER_REWINDDIR

void __tis_mkfs_seekdir (DIR *dirp, long pos) {
  // no error detection (no returned value)
  dirp->__fc_dir_position = pos;
}
#ifndef __TIS_USER_SEEKDIR
void seekdir (DIR *dirp, long pos)
{ __tis_mkfs_seekdir(dirp, pos); }
#endif // __TIS_USER_SEEKDIR

struct dirent *__tis_mkfs_readdir (DIR * restrict dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __tis_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return NULL;
  struct dirent ** dirs = dirp->__fc_dir_entries;
  if (dirs[dirp->__fc_dir_position] == NULL)
    return NULL;
  return dirs[dirp->__fc_dir_position++];
}
#ifndef __TIS_USER_READDIR
struct dirent *readdir (DIR * restrict dirp)
{ return __tis_mkfs_readdir(dirp); }
#endif // __TIS_USER_READDIR

int __tis_mkfs_closedir(DIR * restrict dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __tis_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return res;
  dirp->__fc_dir_inode = NULL;
  __tis_file_desc[fd].__tis_fd_kind = 0;
  return 0;
}
#ifndef __TIS_USER_CLOSEDIR
int closedir(DIR * restrict dirp)
{ return __tis_mkfs_closedir(dirp); }
#endif // __TIS_USER_CLOSEDIR

//==============================================================================
// About pipes
//==============================================================================

int __tis_mkfs_pipe2(int pipefd[2], int flags) {
  int fd = __tis_get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
  if (fd == -1)
    return fd;
  int mode = S_IFIFO | S_IRUSR | S_IWUSR;
  struct stat * st = __tis_mk_inode (mode);

  struct __fc_fs_file *ptr = calloc (1, sizeof(struct __fc_fs_file));
#ifndef __TIS_MKFS_NO_ERR
  if (!ptr) {
    tis_make_unknown(&errno, sizeof errno);
    return -1;
  }
#else
  //@ assert tis_mkfs_pipe2_calloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
  int ret = __tis_open_fd (fd, S_IFIFO, flags | O_RDONLY, NULL, st, ptr);
  if (ret != 0)
    return ret;
  pipefd[0] = fd;
  fd = __tis_get_next_file_desc ();
  if (fd == -1)
    return fd;
  flags |= __tis_translate_mode_string ("w");
  ptr = calloc (1, sizeof(struct __fc_fs_file));
#ifndef __TIS_MKFS_NO_ERR
  if (!ptr) {
    tis_make_unknown(&errno, sizeof errno);
    return -1;
  }
#else
  //@ assert tis_mkfs_pipe2_calloc_ok_2: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
  ret = __tis_open_fd (fd, S_IFIFO, flags, NULL, st, ptr);
  if (ret != 0)
    return ret;
  pipefd[1] = fd;
  return 0;
}
#ifndef __TIS_USER_PIPE2
int pipe2(int pipefd[2], int flags)
{ return __tis_mkfs_pipe2(pipefd, flags); }
#endif // __TIS_USER_PIPE2

int __tis_mkfs_pipe(int pipefd[2]) {
  return pipe2 (pipefd, 0);
}
#ifndef __TIS_USER_PIPE
int pipe(int pipefd[2])
{ return __tis_mkfs_pipe(pipefd); }
#endif // __TIS_USER_PIPE

int __tis_close_fifo (int fd) {
  int res = fclose (&__fc_fopen[fd]);
  free (__fc_fopen[fd].__fc_file);
  __fc_fopen[fd].__fc_file = NULL;
  return res;
}

//==============================================================================
// About sockets
//==============================================================================

int __tis_mkfs_socket(int domain, int type, int protocol) {
  int fd = __tis_get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    __tis_file_desc[fd].__tis_fd_kind = S_IFSOCK;
    __tis_fd_socket[fd].__tis_sock_id = fd;
    __tis_fd_socket[fd].__tis_sock_addr = NULL;
    __tis_fd_socket[fd].__tis_sock_addrlen = 0;
    __tis_fd_socket[fd].__tis_sock_domain = domain;
    __tis_fd_socket[fd].__tis_sock_type = type;
    __tis_fd_socket[fd].__tis_sock_protocol = protocol;
    // __tis_fd_socket[fd].__tis_sock_stat = TODO ?
  }
  return fd;
}
#ifndef __TIS_USER_SOCKET
int socket(int domain, int type, int protocol)
{ return __tis_mkfs_socket(domain, type, protocol); }
#endif // __TIS_USER_SOCKET

int __tis_mkfs_accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
  int ret = __tis_check_fd_socket_ok(sockfd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  int fd = __tis_get_next_file_desc(); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    __tis_file_desc[fd].__tis_fd_kind = S_IFSOCK;
    __tis_fd_socket[fd].__tis_sock_id = fd;
    __tis_fd_socket[fd].__tis_sock_addr =
      malloc(__tis_fd_socket[sockfd].__tis_sock_addrlen);
    __tis_fd_socket[fd].__tis_sock_addrlen =
      __tis_fd_socket[sockfd].__tis_sock_addrlen;
    __tis_fd_socket[fd].__tis_sock_domain =
      __tis_fd_socket[sockfd].__tis_sock_domain;
    __tis_fd_socket[fd].__tis_sock_type =
      __tis_fd_socket[sockfd].__tis_sock_type;
    __tis_fd_socket[fd].__tis_sock_protocol =
      __tis_fd_socket[sockfd].__tis_sock_protocol;
    // __tis_fd_socket[fd].__tis_sock_stat = TODO ?
    tis_make_unknown((char*)__tis_fd_socket[fd].__tis_sock_addr,
        __tis_fd_socket[fd].__tis_sock_addrlen);
    if (addr != NULL) {
      socklen_t len;
      if (*addrlen < __tis_fd_socket[fd].__tis_sock_addrlen)
        len = *addrlen;
      else
        len = __tis_fd_socket[fd].__tis_sock_addrlen;
      *addrlen = len;
      memcpy(addr, __tis_fd_socket[fd].__tis_sock_addr, len);
    }
  }
  return fd;
}
#ifndef __TIS_USER_SOCKET
int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{ return __tis_mkfs_accept(sockfd, addr, addrlen); }
#endif // __TIS_USER_SOCKET

int __tis_mkfs_bind(int fd, const struct sockaddr * addr, socklen_t len) {
  RETURN_RANDOM_ERROR (-1);
  if (__tis_fd_socket[fd].__tis_sock_addr != NULL) {
    errno = EINVAL;
    return -1;
  }
  __tis_fd_socket[fd].__tis_sock_addr = malloc(len);
  memcpy(__tis_fd_socket[fd].__tis_sock_addr, addr, len);
  __tis_fd_socket[fd].__tis_sock_addrlen = len;
  return 0;
}
#ifndef __TIS_USER_BIND
int bind(int fd, const struct sockaddr * addr, socklen_t len)
{ return __tis_mkfs_bind(fd, addr, len); }
#endif // __TIS_USER_BIND

int __tis_mkfs_connect(int fd, const struct sockaddr * addr, socklen_t len) {
  return bind (fd, addr, len); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_CONNECT
int connect(int fd, const struct sockaddr * addr, socklen_t len)
{ return __tis_mkfs_connect(fd, addr, len); }
#endif // __TIS_USER_CONNECT

int __tis_mkfs_getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen) {
  int ret = __tis_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  socklen_t len; /* minimum of *addrlen and __tis_sock_addrlen */
  if (*addrlen < __tis_fd_socket[fd].__tis_sock_addrlen)
    len = *addrlen;
  else
    len = __tis_fd_socket[fd].__tis_sock_addrlen;
  *addrlen = __tis_fd_socket[fd].__tis_sock_addrlen;
  memcpy(addr, __tis_fd_socket[fd].__tis_sock_addr, len);
  return 0;
}
#ifndef __TIS_USER_GETSOCKETNAME
int getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen)
{ return __tis_mkfs_getsockname(fd, addr, addrlen); }
#endif // __TIS_USER_GETSOCKETNAME

ssize_t __tis_mkfs_recv (int fd, void *buf, size_t len, int flags) {
  int ret = __tis_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;

  int n = tis_interval (1, len);
  tis_make_unknown ((char*)buf, n);
  return n;
}
#ifndef __TIS_USER_RECV
ssize_t recv (int fd, void *buf, size_t len, int flags)
{ return __tis_mkfs_recv(fd, buf, len, flags); }
#endif // __TIS_USER_RECV

ssize_t __tis_mkfs_recvfrom (int fd, void *buf, size_t len, int flags,
    struct sockaddr *src_addr, socklen_t *addrlen) {
  int n = recv (fd, buf, len, flags); // handle __TIS_MKFS_NO_ERR
  if (n != -1) {
    int r = getsockname (fd, src_addr, addrlen);
    return r == -1 ? -1 : n;
  }
  return -1;
}
#ifndef __TIS_USER_RECVFROM
ssize_t recvfrom (int fd, void *buf, size_t len, int flags,
    struct sockaddr *src_addr, socklen_t *addrlen)
{ return __tis_mkfs_recvfrom(fd, buf, len, flags, src_addr, addrlen); }
#endif // __TIS_USER_RECVFROM

int __tis_close_socket (struct __tis_socket * sock) {
  int fd = sock->__tis_sock_id;
  int ret = __tis_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;

  __tis_file_desc [fd].__tis_fd_kind = 0;
  if (__tis_fd_socket[fd].__tis_sock_addr != NULL)
    free(__tis_fd_socket[fd].__tis_sock_addr);
  return 0;
}
//==============================================================================

int __tis_mkfs_close(int fd) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  switch ( __tis_file_desc[fd].__tis_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO: return __tis_close_fifo (fd);
    case S_IFREG: return fclose (&__fc_fopen[fd]);
    case S_IFDIR: return closedir (&__fc_opendir[fd]);
    case S_IFSOCK: return __tis_close_socket (&__tis_fd_socket[fd]);
    case S_IFCHR:
                   __tis_file_desc[fd].__tis_fd_kind = 0;
                   return 0;
    default: tis_make_unknown(&errno, sizeof errno);
             return -1;
  }
}
#ifndef __TIS_USER_CLOSE
int close(int fd)
{ return __tis_mkfs_close(fd); }
#endif // __TIS_USER_CLOSE

//==============================================================================
// Remove files and directories
//==============================================================================
// set errno when \result == -1;
int __tis_rm_file (int f) {
  RETURN_RANDOM_ERROR (-1);

  // TODO
  printf ("NIY WARNING: unlinked file not being removed from dirent\n");
  //@ assert rm_file_not_dirent_mkfs_niy: WARN_NIY ;

  __fc_fs_files [f].__fc_fullpath = NULL;
  __fc_fs_files [f].__fc_stat = NULL;
  __fc_fs_files [f].__fc_content = NULL;
  return 0;
}
// set errno when \result == -1;
int __tis_rm_dir (int d) {
#ifndef __TIS_MKFS_NO_ERR
  if (tis_nondet (0, 1)) {
    tis_make_unknown(&errno, sizeof errno);
    return -1;
  }
#endif // __TIS_MKFS_NO_ERR
  if (__fc_fs_dirs [d].__fc_dir_entries[2]) {
    // not empty (entry 0 is for '.' and 1 for '..')
    errno = ENOTEMPTY;
    return -1;
  }

  // This is to warn that the directory is removed from the directory table,
  // but not removed form its parent directory entries.
  //@ assert rm_dir_not_dirent_mkfs_niy: WARN_NIY ;

  __fc_fs_dirs [d].__fc_fullpath = NULL;
  __fc_fs_dirs [d].__fc_stat = NULL;
  __fc_fs_dirs [d].__fc_dir_entries = NULL;
  return 0;
}

// TODO: implement link, which requires a bit of work: we need to stop
// storing the file name in __fc_fs_file, since __fc_fs_file is really
// an inode. the file name(s) need to move into directory entries.
int __tis_mkfs_link(const char *oldpath, const char *newpath) {
  //@ assert link_mkfs_niy: WARN_NIY ;
  return -1;
}
#ifndef __TIS_USER_LINK
int link(const char *oldpath, const char *newpath)
{ return __tis_mkfs_link(oldpath, newpath); }
#endif // __TIS_USER_LINK

// set errno when \result == -1;
int __tis_mkfs_unlink(const char *pathname) {
  int f = __tis_mkfs_get_file (pathname);
  if (f == -1) {
    errno = ENOENT;
    return -1;
  }
  return __tis_rm_file (f);
}
#ifndef __TIS_USER_UNLINK
int unlink(const char *pathname)
{ return __tis_mkfs_unlink(pathname); }
#endif // __TIS_USER_UNLINK

// set errno when \result == -1;
ssize_t __tis_mkfs_readlink(const char *path, char *buf, size_t bufsiz) {
  // TODO: support symbolic links
  errno = EINVAL;
  return -1;
}

#ifndef __TIS_USER_READLINK
ssize_t readlink(const char *path, char *buf, size_t bufsiz)
{ return __tis_mkfs_readlink(path, buf, bufsiz); }
#endif // __TIS_USER_READLINK

char *__tis_mkfs_getcwd(char *buf, size_t size) {
  static char *cwd = "/";
  if (size < 1 + strlen(cwd)) {
    errno = ERANGE;
    return NULL;
  }
  strcpy(buf, cwd);
  return cwd;
}

#ifndef __TIS_USER_GETCWD
char *getcwd(char *buf, size_t size)
{ return __tis_mkfs_getcwd(buf, size); }
#endif // __TIS_USER_GETCWD

int __tis_mkfs_rmdir(const char *pathname) {
  int d = __tis_mkfs_get_dir (pathname);
  if (d != -1)
    return __tis_rm_dir (d); // handle __TIS_MKFS_NO_ERR
  tis_make_unknown(&errno, sizeof errno);
  return -1;
}
#ifndef __TIS_USER_RMDIR
int rmdir(const char *pathname)
{ return __tis_mkfs_rmdir(pathname); }
#endif // __TIS_USER_RMDIR

// set errno when \result == -1;
int __tis_mkfs_remove(const char *pathname) {
  int f = __tis_mkfs_get_file (pathname);
  if (f != -1)
    return __tis_rm_file (f); // handle __TIS_MKFS_NO_ERR
  int d = __tis_mkfs_get_dir (pathname);
  if (d != -1)
    return __tis_rm_dir (d); // handle __TIS_MKFS_NO_ERR
  tis_make_unknown(&errno, sizeof errno);
  return -1;
}
#ifndef __TIS_USER_REMOVE
int remove(const char *pathname)
{ return __tis_mkfs_remove(pathname); }
#endif // __TIS_USER_REMOVE

//==============================================================================
// Temporary files
//==============================================================================

// P_tmpdir should be defined in stdio.h
#define P_tmpdir "/tmp/tmp_"

char *__tis_mkfs_tmpnam(char *s) {
  static char buf[L_tmpnam];
  int n = strlen (P_tmpdir);
  if (n + 6 >= L_tmpnam)
    return NULL;
  strncpy(buf, P_tmpdir, n);
  char c;
  for (c = 'a'; c <= 'z'; c++) {
    buf[n] = c;
    int f = __tis_mkfs_get_file (buf);
    if (f == -1)
      break;
  }
#ifndef __TIS_MKFS_NO_ERR
  if (tis_nondet (0, 1)) {
    tis_make_unknown(&errno, sizeof errno);
    return NULL;
  }
#endif // __TIS_MKFS_NO_ERR
  //@ assert tmpnam_mkfs_niy: c <= 'z';
  buf[n+1] = 0;
  if (s)
    strncpy(s, buf, n+2);
  else
    s = buf;
  return s;
}
#ifndef __TIS_USER_TMPNAM
char *tmpnam(char *s)
{ return __tis_mkfs_tmpnam(s); }
#endif // __TIS_USER_TMPNAM

int __tis_mkfs_mkstemp(char *template) {
  char *tmp= template + strlen(template) - 6;
  if (tmp<template) {
    errno=EINVAL;
    return -1;
  }
  for (int nx =0; nx <6; nx ++) {
    if (tmp[nx ]!='X') {
      errno=EINVAL;
      return -1;
    }
  }
  for (int nx =0; nx <6; nx ++) {
    tmp[nx ] = 'a';
  }

  int f;
  for (int nx =0; nx <6; nx ++) {
    for (char c = 'a'; c <= 'z'; c++) {
      tmp[nx] = c;
      f = __tis_mkfs_get_file (template);
      if (f == -1) // file does not exist yet
        break;
    }
  }
  if (f != -1) {
    errno = EEXIST;
    return -1;
  }
  int flags = O_CREAT|O_RDWR|O_EXCL|O_NOFOLLOW;
  int fd = __tis_open_file (template,flags,0600); // handle __TIS_MKFS_NO_ERR
  return fd;
}
#ifndef __TIS_USER_MKSTEMP
int mkstemp(char *template)
{ return __tis_mkfs_mkstemp(template); }
#endif // __TIS_USER_MKSTEMP

FILE *__tis_mkfs_tmpfile(void) {
  char template[] = "/tmp/tmpfile-XXXXXX";
  int fd = mkstemp(template); // handle __TIS_MKFS_NO_ERR
  if (fd < 0)
    return NULL;
  return &__fc_fopen[fd];
}
#ifndef __TIS_USER_TMPFILE
FILE *tmpfile(void)
{ return __tis_mkfs_tmpfile(); }
#endif // __TIS_USER_TMPFILE

//==============================================================================
// mmap/munmap
//==============================================================================

#define MMAP_MAX FOPEN_MAX

typedef struct __fc_map {
  unsigned char * data;
  void * addr;
  size_t length;
  bool shared;
  bool need_sync;
} map;
struct __fc_maps {
  struct __fc_map maps[MMAP_MAX];
  size_t nb_used;
} maps;

static map * find_data_map (void * data) {
  //@ slevel 1000000;
  for (size_t i = 0; i < maps.nb_used; i++) {
    if (maps.maps[i].data == data)
      return maps.maps + i;
  }
  //@ slevel default;
  return NULL;
}
static map * find_addr_map (void * addr, size_t length) {
  //@ slevel 1000000;
  for (size_t i = 0; i < maps.nb_used; i++) {
    if (maps.maps[i].addr == addr && maps.maps[i].length == length)
      return maps.maps + i;
  }
  //@ slevel default;
  return NULL;
}
static void * add_map (unsigned char * data, size_t length,
    bool shared, bool need_sync) {
  if (shared) { // check if already in.
    map * map = find_data_map (data);
    if (map)
      return map->addr;
  }
  if (maps.nb_used >= MMAP_MAX) {
    errno = ENOMEM;
    return MAP_FAILED;
  }
  size_t m = maps.nb_used++;
  void * addr = malloc (length); // TODO: should be calloc (n, PAGE_SIZE)
#ifdef __TIS_MKFS_NO_ERR
  //@ assert tis_mkfs_mmap_malloc_ok: addr != \null;
#else
  if (addr == NULL) {
    errno = ENOMEM;
    return MAP_FAILED;
  }
#endif
  // TODO: use a builtin to make the location read-only is needed.
  maps.maps[m].data = data;
  maps.maps[m].addr = memcpy (addr, data, length);
  maps.maps[m].length = length;
  maps.maps[m].shared = shared;
  maps.maps[m].need_sync = need_sync;
  return addr;
}


// set errno when \result == -1;
int __tis_check_mmap_prot (int fd, int prot) {
  // fd needs read permission, regardless of the protection options specified.
  int ret = __tis_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) return ret; // errno already set
  if (prot == PROT_NONE) {
    //@ assert mmap_prot_none_mkfs_niy: WARN_NIY ;
    return -1;
  }
  if (prot & PROT_EXEC) {
    //@ assert mmap_prot_exec_mkfs_niy: WARN_NIY ;
  }
  if (prot & PROT_WRITE) {
    ret = __tis_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
    return ret; // errno already set when ret != 0
  }
  else { // PROT_READ only
    return 0;
  }
}

/* This is a limited version of 'mmap' that only handle
   - offset == 0, length == size of the underlying file;
   - flags == MAP_SHARED || flags == MAP_PRIVATE
   - prot holds only PROT_READ, PROT_WRITE, or both.

   Moreover, the size of the map should be a multiple of the page size,
   with the bytes outside the file set to 0. At the moment,
   the allocated map has the same size than the file.
   This can be considered as an extra protection.

   If the content of a mapped file is modified,
   it is not propagated to the map.
   With the MAP_PRIVATE mode, it is ok since the behavior is explicitly
   unspecified.
   With the MAP_SHARED mode, it is unclear (TODO: find out what should be done)
   */
void * __tis_mkfs_mmap(void *addr, size_t length, int prot, int flags,
    int fd, off_t offset) {
  if (flags & MAP_FIXED) {
    //@ assert mmap_map_fixed_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }
  // when flags does not hold MAP_FIXED,
  // addr is only a hint, so we can ignore it.
  if (offset != 0) {
    //@ assert mmap_offset_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }

  FILE * file = __fc_fopen + fd;
  struct stat * st = file->__fc_inode;
  if (length != st->st_size) {
    //@ assert mmap_length_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }

  if (__tis_check_mmap_prot (fd, prot) != 0) {
    return MAP_FAILED;
  }

  if (flags & MAP_SHARED == flags & MAP_PRIVATE) {
    // both on or both off : forbiden
    errno = EINVAL;
    return MAP_FAILED;
  }
  if (flags != flags & (MAP_SHARED | MAP_PRIVATE)) {
    //@ assert mmap_other_flags_mkfs_niy: WARN_NIY ;
  }

  RETURN_RANDOM_ERROR (MAP_FAILED);

  if (flags & MAP_SHARED) {
    bool writable = prot&PROT_WRITE;
    return add_map (file->__fc_file->__fc_data, length, true, writable);
  }
  else { // (flags & MAP_PRIVATE)
    return add_map (file->__fc_file->__fc_data, length, false, false);
  }
}

#ifndef __TIS_USER_MMAP
void *mmap(void *addr, size_t length, int prot, int flags,
    int fd, off_t offset) {
  return __tis_mkfs_mmap(addr, length, prot, flags, fd, offset);
}
#endif

//@ requires msync_no_need_sync: map->need_sync;
static void msync_map_to_file (map * map) {
  memcpy (map->data, map->addr, map->length);
}

/* munmap() deletes the mappings for the specified address range,
   i.e. unmap all the pages containing a part of addr[0..length].
   The man page says is normally not an error if the indicated range
   does not contain any mapped pages, but POSIX seems to enforce that
   (addr, length) has to come from a previous `mmap` call,
   so do we here. */
int __tis_mkfs_munmap(void *addr, size_t length) {
  RETURN_RANDOM_ERROR (-1);
  map * map = find_addr_map (addr, length);
  if (map) {
    // TODO: call msync(MS_SYNC) when required (ie MAP_SHARED+PROT_WRITE)
    if (map->need_sync)
      msync_map_to_file (map);
    free (map->addr);
    map->data = NULL; map->addr = NULL; map->length = 0;
    // maps.maps[] is not packed and maps.nb_used in not decreased here
    // on purpose to avoid using the same element for different purposes,
    // which may lead to imprecision in the analyses.
    return 0;
  }
  else {
    return -1;
  }
}

#ifndef __TIS_USER_MUNMAP
int munmap(void *addr, size_t length) {
  return __tis_mkfs_munmap(addr, length);
}
#endif

#ifndef __TIS_USER_MSYNC
int msync(void *addr, size_t length, int flags) {
  if ((flags & MS_ASYNC) == (flags & MS_SYNC)) {
    // both on or both off : forbiden
    errno = EINVAL;
    return -1;
  }
  if (flags != flags & (MS_ASYNC & MS_SYNC & MS_INVALIDATE)) {
    errno = EINVAL;
    return -1;
  }
  if (flags & MS_INVALIDATE) {
    //@ assert msync_invalidate_mkfs_niy: \false;
  }

  map * map = find_addr_map (addr, length);
  if (map) {
    // flags already verified above.
    msync_map_to_file (map);
    return 0;
  }
  else {
    errno = ENOMEM;
    return -1;
  }
}
#endif

//==============================================================================
// END.
//==============================================================================
