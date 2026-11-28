/*
 * gtcoh: CPU/GT cache coherence experiments on an Intel GEN12 GPU, run as an
 * ordinary DRM client through the i915 uapi.
 *
 * Experiments (one "mode" each):
 *   hc17          CPU -> GT, soundness. Source object with caching CACHED (LLC).
 *                 The CPU writes a fresh pattern through a write-back mapping
 *                 with no set_domain and no flush; the copy engine copies
 *                 source -> destination; the CPU checks the destination.
 *   hc17-partner  The same with the source's caching set to NONE (sensitivity).
 *   hg5           GT -> CPU, soundness. The CPU first reads the destination
 *                 through a write-back mapping (warming its cache), the copy
 *                 engine writes it, and after the wait the CPU reads it again
 *                 through the same mapping with no set_domain.
 *   hg5-partner   The same with the destination's caching set to NONE.
 *   checker       hc17's objects, but the CPU reads the destination right
 *                 after submitting, before the blit can have finished: the
 *                 check itself must report stale words (sensitivity of the
 *                 checker, not of coherence; on a shared-LLC GPU the GT
 *                 snoops the CPU caches even with caching NONE, so the two
 *                 partners above cannot fire there).
 *
 * The program never touches registers, never reloads a module and never uses
 * the display. All GPU work is one copy-engine batch per iteration with
 * softpinned 48-bit addresses (no relocations) and a bounded GEM wait.
 *
 * The blit command is XY_FAST_COPY_BLT, encoded from the Intel Graphics PRM
 * for Tiger Lake (doc ref IHD-OS-TGL-Vol 2a-12.21, "XY_FAST_COPY_BLT",
 * printed pages 1371-1373), with the pitch unit from IHD-OS-TGL-Vol 10-12.21,
 * "2D (XY) BLT Instructions" (printed page 40: linear pitch in bytes).
 *
 * Exit codes:
 *   0  every requested mode ran; no stale data in a soundness mode
 *   1  usage error
 *   2  no i915 device found
 *   3  permission denied opening the device
 *   4  the driver refused a feature the experiment needs
 *   5  GPU submission error or wait timeout
 *   6  stale data seen in a soundness mode (hc17 or hg5)
 */
#define _GNU_SOURCE
#include <drm/drm.h>
#include <drm/i915_drm.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

enum {
  EXIT_OK = 0,
  EXIT_USAGE = 1,
  EXIT_NODEV = 2,
  EXIT_PERM = 3,
  EXIT_UNSUPPORTED = 4,
  EXIT_GPU = 5,
  EXIT_STALE = 6,
};

/* Softpinned GPU virtual addresses in the client's own (full) PPGTT. All are
 * canonical 48-bit addresses above 4 GiB and 64 KiB aligned. */
#define BATCH_VA 0x0000000100000000ull
#define SRC_VA 0x0000000200000000ull
#define DST_VA 0x0000000300000000ull
/* Each mode uses fresh objects at addresses moved by mode * MODE_VA_STEP, so
 * that no address is reused while i915 may still hold a closed object's
 * binding. */
#define MODE_VA_STEP 0x0000001000000000ull

#define PITCH_BYTES 4096u /* one surface row; 1024 pixels at 32 bpp */
#define BATCH_DWORDS 12
#define BATCH_BYTES 4096u

/* ---- Command encoding (PRM Vol 2a / Vol 10, see the header comment) ---- */

/* XY_FAST_COPY_BLT, DWord 0 (BR00). */
#define FC_CLIENT_2D (2u << 29)         /* 31:29 Client = 02h 2D Processor */
#define FC_OPCODE (0x42u << 22)         /* 28:22 Instruction Target = 42h */
#define FC_SRC_TILING_LINEAR (0u << 20) /* 21:20 Source Tiling = 00b Linear */
#define FC_DST_TILING_LINEAR (0u << 13) /* 14:13 Dest Tiling = 00b Linear */
#define FC_DWORD_LENGTH 8u              /* 7:0 DWord Length = 08h (bias 2) */
/* XY_FAST_COPY_BLT, DWord 1 (BR13). */
#define FC_DEPTH_32 (3u << 24) /* 26:24 Color Depth = 011b 32 bit color */
/* MI_BATCH_BUFFER_END (Vol 2a, printed page 965): Command Type 31:29 = 0
 * (MI_COMMAND), MI Command Opcode 28:23 = 0Ah, End Context bit 0 = 0. */
#define MI_BBE (0x0au << 23)
/* MI_NOOP (Vol 2a, printed page 1025): every field 0. */
#define MI_NOP 0u

static void build_batch(uint32_t *b, uint32_t size_bytes, uint64_t va_off) {
  const uint64_t dst_va = DST_VA + va_off, src_va = SRC_VA + va_off;
  uint32_t width_px = PITCH_BYTES / 4u;
  uint32_t height = size_bytes / PITCH_BYTES;
  b[0] = FC_CLIENT_2D | FC_OPCODE | FC_SRC_TILING_LINEAR |
         FC_DST_TILING_LINEAR | FC_DWORD_LENGTH;
  /* DW1: 31 src Tile-Y type 0, 30 dst Tile-Y type 0, 29:27 MBZ,
   * 26:24 color depth, 23:16 MBZ, 15:0 destination pitch (bytes, linear). */
  b[1] = FC_DEPTH_32 | PITCH_BYTES;
  /* DW2 (BR22): 31:16 destination Y1 (top, inclusive), 15:0 X1 (left). */
  b[2] = 0;
  /* DW3 (BR23): 31:16 destination Y2 (bottom, exclusive), 15:0 X2 (right,
   * exclusive, in pixels). Neither width nor height may be 0 (Vol 10). */
  b[3] = (height << 16) | width_px;
  /* DW4..5: destination base address, 64-byte aligned. */
  b[4] = (uint32_t)dst_va;
  b[5] = (uint32_t)(dst_va >> 32);
  /* DW6 (BR26): 31:16 source Y1, 15:0 source X1. */
  b[6] = 0;
  /* DW7 (BR11): 31:16 MBZ, 15:0 source pitch (bytes, linear). */
  b[7] = PITCH_BYTES;
  /* DW8..9: source base address, 64-byte aligned. */
  b[8] = (uint32_t)src_va;
  b[9] = (uint32_t)(src_va >> 32);
  b[10] = MI_BBE;
  b[11] = MI_NOP; /* pad the batch to a QWord boundary */
}

static const char *const batch_notes[BATCH_DWORDS] = {
    "XY_FAST_COPY_BLT DW0: client 2 (2D) [31:29], opcode 42h [28:22], "
    "src tiling linear [21:20], dst tiling linear [14:13], length 8 [7:0]",
    "DW1: color depth 32 bpp [26:24]=011b, dst pitch [15:0] bytes",
    "DW2: dst Y1 [31:16]=0, dst X1 [15:0]=0",
    "DW3: dst Y2 [31:16]=rows (exclusive), dst X2 [15:0]=pixels (exclusive)",
    "DW4: dst base address [31:0]",
    "DW5: dst base address [63:32]",
    "DW6: src Y1 [31:16]=0, src X1 [15:0]=0",
    "DW7: src pitch [15:0] bytes, [31:16] MBZ",
    "DW8: src base address [31:0]",
    "DW9: src base address [63:32]",
    "MI_BATCH_BUFFER_END: type 0 [31:29], opcode 0Ah [28:23]",
    "MI_NOOP: padding to a QWord boundary",
};

/* ---- Options ---- */

enum mode_id { M_HC17, M_HC17P, M_HG5, M_HG5P, M_CHECK, M_COUNT };

static const char *const mode_names[M_COUNT] = {"hc17", "hc17-partner", "hg5",
                                                "hg5-partner", "checker"};

struct options {
  uint64_t iters;
  uint32_t size;
  int modes[M_COUNT];
  int stress;
  uint32_t stress_mib;
  uint64_t timeout_ns;
  double max_seconds;
  const char *device;
  int dry_run;
  int verbose;
};

static void usage(FILE *f) {
  fprintf(f,
          "usage: gtcoh [options]\n"
          "  --mode LIST       comma-separated: hc17,hc17-partner,hg5,"
          "hg5-partner,checker,all (default all)\n"
          "  --iters N         iterations per mode (default 100000)\n"
          "  --size BYTES      object size, multiple of 4096, at most 64 MiB "
          "(default 65536)\n"
          "  --stress          run a second thread streaming through a buffer "
          "larger than the LLC\n"
          "  --stress-mib N    size of that buffer in MiB (default 64)\n"
          "  --timeout-ms N    bound on each GEM wait (default 5000)\n"
          "  --max-seconds S   bound on each mode's run time (default 600)\n"
          "  --device PATH     DRM node to use (default: first i915 render "
          "node, then card node)\n"
          "  --dry-run         print the batch and the exec objects; open no "
          "device\n"
          "  --verbose         print the first mismatches of each mode\n"
          "  --help            this text\n"
          "Exit codes: 0 ok, 1 usage, 2 no i915 device, 3 permission denied,\n"
          "4 feature refused by the driver, 5 GPU error or timeout,\n"
          "6 stale data in a soundness mode.\n");
}

static int parse_u64(const char *s, uint64_t *out) {
  char *end;
  errno = 0;
  unsigned long long v = strtoull(s, &end, 0);
  if (errno || end == s || *end) return -1;
  *out = v;
  return 0;
}

static int parse_modes(const char *s, int *modes) {
  char buf[256];
  if (strlen(s) >= sizeof buf) return -1;
  strcpy(buf, s);
  memset(modes, 0, sizeof(int) * M_COUNT);
  for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) {
    if (!strcmp(tok, "all")) {
      for (int i = 0; i < M_COUNT; i++) modes[i] = 1;
      continue;
    }
    int found = 0;
    for (int i = 0; i < M_COUNT; i++)
      if (!strcmp(tok, mode_names[i])) modes[i] = found = 1;
    if (!found) return -1;
  }
  return 0;
}

static int parse_args(int argc, char **argv, struct options *o) {
  memset(o, 0, sizeof *o);
  o->iters = 100000;
  o->size = 65536;
  o->stress_mib = 64;
  o->timeout_ns = 5000ull * 1000000ull;
  o->max_seconds = 600;
  for (int i = 0; i < M_COUNT; i++) o->modes[i] = 1;
  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    const char *v = i + 1 < argc ? argv[i + 1] : NULL;
    uint64_t n;
    if (!strcmp(a, "--help") || !strcmp(a, "-h")) {
      usage(stdout);
      exit(EXIT_OK);
    } else if (!strcmp(a, "--dry-run")) {
      o->dry_run = 1;
    } else if (!strcmp(a, "--stress")) {
      o->stress = 1;
    } else if (!strcmp(a, "--verbose")) {
      o->verbose = 1;
    } else if (!v) {
      fprintf(stderr, "gtcoh: missing value or unknown option %s\n", a);
      return -1;
    } else if (!strcmp(a, "--mode")) {
      if (parse_modes(v, o->modes)) {
        fprintf(stderr, "gtcoh: bad --mode %s\n", v);
        return -1;
      }
      i++;
    } else if (!strcmp(a, "--device")) {
      o->device = v;
      i++;
    } else if (parse_u64(v, &n)) {
      fprintf(stderr, "gtcoh: bad number for %s: %s\n", a, v);
      return -1;
    } else if (!strcmp(a, "--iters")) {
      if (n == 0) return -1;
      o->iters = n;
      i++;
    } else if (!strcmp(a, "--size")) {
      if (n < 4096 || n % 4096 || n > (64u << 20)) {
        fprintf(stderr, "gtcoh: --size must be a multiple of 4096 in "
                        "[4096, 64 MiB]\n");
        return -1;
      }
      o->size = (uint32_t)n;
      i++;
    } else if (!strcmp(a, "--stress-mib")) {
      if (n == 0 || n > 4096) return -1;
      o->stress_mib = (uint32_t)n;
      i++;
    } else if (!strcmp(a, "--timeout-ms")) {
      if (n == 0 || n > 600000) return -1;
      o->timeout_ns = n * 1000000ull;
      i++;
    } else if (!strcmp(a, "--max-seconds")) {
      if (n == 0) return -1;
      o->max_seconds = (double)n;
      i++;
    } else {
      fprintf(stderr, "gtcoh: unknown option %s\n", a);
      return -1;
    }
  }
  return 0;
}

/* ---- Dry run ---- */

static void dry_run(const struct options *o) {
  uint32_t b[BATCH_DWORDS];
  build_batch(b, o->size, 0);
  printf("gtcoh dry run: no device opened\n");
  printf("object size %u bytes = %u rows x %u bytes (32 bpp, linear)\n",
         o->size, o->size / PITCH_BYTES, PITCH_BYTES);
  printf("batch: %d dwords at 0x%016" PRIx64 ", engine I915_EXEC_BLT, "
         "flags NO_RELOC\n",
         BATCH_DWORDS, (uint64_t)BATCH_VA);
  for (int i = 0; i < BATCH_DWORDS; i++)
    printf("  [%2d] 0x%08x  %s\n", i, b[i], batch_notes[i]);
  printf("exec objects (in order; the batch is last):\n");
  printf("  0 src   offset 0x%016" PRIx64 " size %u flags PINNED|48B\n",
         (uint64_t)SRC_VA, o->size);
  printf("  1 dst   offset 0x%016" PRIx64 " size %u flags PINNED|48B|WRITE\n",
         (uint64_t)DST_VA, o->size);
  printf("  2 batch offset 0x%016" PRIx64 " size %u flags PINNED|48B\n",
         (uint64_t)BATCH_VA, BATCH_BYTES);
  printf("(shown for the first mode; mode k adds k * 0x%" PRIx64
         " to every address)\n", (uint64_t)MODE_VA_STEP);
  printf("modes:");
  for (int i = 0; i < M_COUNT; i++)
    if (o->modes[i]) printf(" %s", mode_names[i]);
  printf("\niterations per mode %" PRIu64 ", stress %s\n", o->iters,
         o->stress ? "on" : "off");
}

/* ---- DRM helpers ---- */

static int xioctl(int fd, unsigned long req, void *arg) {
  int r;
  do {
    r = ioctl(fd, req, arg);
  } while (r == -1 && (errno == EINTR || errno == EAGAIN));
  return r;
}

static int is_i915(int fd) {
  char name[32] = {0};
  struct drm_version v;
  memset(&v, 0, sizeof v);
  v.name = name;
  v.name_len = sizeof name - 1;
  if (xioctl(fd, DRM_IOCTL_VERSION, &v)) return 0;
  return strcmp(name, "i915") == 0;
}

/* Returns an fd, or -EXIT_NODEV / -EXIT_PERM. */
static int open_device(const char *path, char *used, size_t used_len) {
  int saw_perm = 0;
  if (path) {
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) {
      fprintf(stderr, "gtcoh: cannot open %s: %s\n", path, strerror(errno));
      return errno == EACCES || errno == EPERM ? -EXIT_PERM : -EXIT_NODEV;
    }
    if (!is_i915(fd)) {
      fprintf(stderr, "gtcoh: %s is not an i915 device\n", path);
      close(fd);
      return -EXIT_NODEV;
    }
    snprintf(used, used_len, "%s", path);
    return fd;
  }
  static const struct {
    const char *fmt;
    int first, last;
  } nodes[] = {{"/dev/dri/renderD%d", 128, 191}, {"/dev/dri/card%d", 0, 63}};
  for (size_t k = 0; k < sizeof nodes / sizeof nodes[0]; k++) {
    for (int n = nodes[k].first; n <= nodes[k].last; n++) {
      char p[64];
      snprintf(p, sizeof p, nodes[k].fmt, n);
      int fd = open(p, O_RDWR | O_CLOEXEC);
      if (fd < 0) {
        if (errno == EACCES || errno == EPERM) saw_perm = 1;
        continue;
      }
      if (is_i915(fd)) {
        snprintf(used, used_len, "%s", p);
        return fd;
      }
      close(fd);
    }
  }
  if (saw_perm) {
    fprintf(stderr, "gtcoh: permission denied on a DRM node; run as root "
                    "or as a member of the render group\n");
    return -EXIT_PERM;
  }
  fprintf(stderr, "gtcoh: no i915 device found under /dev/dri\n");
  return -EXIT_NODEV;
}

static int getparam(int fd, int param, int *value) {
  struct drm_i915_getparam gp;
  memset(&gp, 0, sizeof gp);
  gp.param = param;
  gp.value = value;
  return xioctl(fd, DRM_IOCTL_I915_GETPARAM, &gp);
}

static int gem_create(int fd, uint64_t size, uint32_t *handle) {
  struct drm_i915_gem_create c;
  memset(&c, 0, sizeof c);
  c.size = size;
  if (xioctl(fd, DRM_IOCTL_I915_GEM_CREATE, &c)) return -1;
  *handle = c.handle;
  return 0;
}

static void gem_close(int fd, uint32_t handle) {
  struct drm_gem_close c;
  memset(&c, 0, sizeof c);
  c.handle = handle;
  xioctl(fd, DRM_IOCTL_GEM_CLOSE, &c);
}

static int gem_set_caching(int fd, uint32_t handle, uint32_t caching) {
  struct drm_i915_gem_caching c;
  memset(&c, 0, sizeof c);
  c.handle = handle;
  c.caching = caching;
  return xioctl(fd, DRM_IOCTL_I915_GEM_SET_CACHING, &c);
}

static int gem_set_domain(int fd, uint32_t handle, uint32_t read,
                          uint32_t write) {
  struct drm_i915_gem_set_domain d;
  memset(&d, 0, sizeof d);
  d.handle = handle;
  d.read_domains = read;
  d.write_domain = write;
  return xioctl(fd, DRM_IOCTL_I915_GEM_SET_DOMAIN, &d);
}

/* Write-back CPU mapping through I915_GEM_MMAP_OFFSET. */
static void *gem_mmap_wb(int fd, uint32_t handle, uint64_t size) {
  struct drm_i915_gem_mmap_offset m;
  memset(&m, 0, sizeof m);
  m.handle = handle;
  m.flags = I915_MMAP_OFFSET_WB;
  if (xioctl(fd, DRM_IOCTL_I915_GEM_MMAP_OFFSET, &m)) return NULL;
  void *p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd,
                 (off_t)m.offset);
  return p == MAP_FAILED ? NULL : p;
}

/* Copies `size` bytes into an object through a write-back mapping, in i915's
 * CPU write domain, so that the next execbuf makes them visible to the GT.
 * (i915 refuses GEM_PWRITE on graphics version 12 and later, except Tiger
 * Lake.) Returns 0, or -1 with errno. */
static int gem_write(int fd, uint32_t handle, const void *data,
                     uint64_t size) {
  void *p = gem_mmap_wb(fd, handle, size);
  if (!p) return -1;
  int rc = gem_set_domain(fd, handle, I915_GEM_DOMAIN_CPU, I915_GEM_DOMAIN_CPU);
  if (rc == 0) memcpy(p, data, size);
  int e = errno;
  munmap(p, size);
  errno = e;
  return rc;
}

/* Returns 0, or -1 with errno (ETIME on timeout). */
static int gem_wait(int fd, uint32_t handle, uint64_t timeout_ns) {
  struct drm_i915_gem_wait w;
  memset(&w, 0, sizeof w);
  w.bo_handle = handle;
  w.timeout_ns = (int64_t)timeout_ns;
  return xioctl(fd, DRM_IOCTL_I915_GEM_WAIT, &w);
}

/* ---- Stress thread ---- */

static volatile int stress_stop;

static void *stress_main(void *arg) {
  size_t bytes = (size_t)(uintptr_t)arg;
  volatile uint64_t *buf = malloc(bytes);
  if (!buf) return NULL;
  size_t n = bytes / sizeof(uint64_t);
  uint64_t k = 0;
  while (!stress_stop) {
    for (size_t i = 0; i < n && !stress_stop; i += 8) /* one 64-byte line */
      buf[i] = buf[i] + ++k;
  }
  free((void *)buf);
  return NULL;
}

/* ---- Experiment ---- */

static inline uint32_t pattern(uint64_t it, uint32_t i) {
  /* it == 0 is the object's initial content (GEM objects start zeroed). */
  if (it == 0) return 0;
  return (uint32_t)(it * 0x9e3779b1u) ^ (i * 0x85ebca77u) ^ 0x5a5a5a5au;
}

static double now_s(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

struct result {
  uint64_t iters, stale, other, errors;
  int64_t first_stale;
  int fatal; /* exit code if the mode could not run */
};

/* Compares the destination with iteration `it`'s pattern and counts the
 * iteration as stale (a word holds the previous pattern) and/or other. */
static void check_dst(const struct options *o, enum mode_id m,
                      volatile uint32_t *vd, uint32_t words, uint64_t it,
                      struct result *r, int *printed) {
  uint32_t bad_stale = 0, bad_other = 0;
  for (uint32_t i = 0; i < words; i++) {
    uint32_t v = vd[i];
    if (v == pattern(it, i)) continue;
    if (v == pattern(it - 1, i))
      bad_stale++;
    else
      bad_other++;
    if (o->verbose && *printed < 8) {
      (*printed)++;
      fprintf(stderr, "gtcoh: %s: iter %" PRIu64 " word %u: got 0x%08x "
                      "want 0x%08x prev 0x%08x\n", mode_names[m], it, i, v,
              pattern(it, i), pattern(it - 1, i));
    }
  }
  if (bad_stale) {
    r->stale++;
    if (r->first_stale < 0) r->first_stale = (int64_t)it;
  }
  if (bad_other) r->other++;
}

static int run_mode(int fd, const struct options *o, enum mode_id m,
                    struct result *r) {
  const int gt_reads_cpu = (m == M_HC17 || m == M_HC17P || m == M_CHECK);
  /* checker: read the destination before waiting for the blit. */
  const int early = (m == M_CHECK);
  /* Caching of the object under test; the other object uses the setting
   * i915's own coherent path handles (see README). */
  uint32_t src_caching, dst_caching;
  switch (m) {
  case M_HC17:
  case M_CHECK: src_caching = I915_CACHING_CACHED; dst_caching = I915_CACHING_CACHED; break;
  case M_HC17P: src_caching = I915_CACHING_NONE; dst_caching = I915_CACHING_CACHED; break;
  case M_HG5: src_caching = I915_CACHING_NONE; dst_caching = I915_CACHING_CACHED; break;
  default: src_caching = I915_CACHING_NONE; dst_caching = I915_CACHING_NONE; break;
  }
  memset(r, 0, sizeof *r);
  r->first_stale = -1;
  const uint32_t words = o->size / 4;
  uint32_t hs = 0, hd = 0, hb = 0;
  uint32_t *src = NULL, *dst = NULL;
  int rc = 0;
  double t0 = now_s();

  if (gem_create(fd, o->size, &hs) || gem_create(fd, o->size, &hd) ||
      gem_create(fd, BATCH_BYTES, &hb)) {
    fprintf(stderr, "gtcoh: GEM_CREATE failed: %s\n", strerror(errno));
    rc = EXIT_UNSUPPORTED;
    goto out;
  }
  if (gem_set_caching(fd, hs, src_caching) ||
      gem_set_caching(fd, hd, dst_caching)) {
    fprintf(stderr, "gtcoh: GEM_SET_CACHING failed: %s\n", strerror(errno));
    rc = EXIT_UNSUPPORTED;
    goto out;
  }
  src = gem_mmap_wb(fd, hs, o->size);
  dst = gem_mmap_wb(fd, hd, o->size);
  if (!src || !dst) {
    fprintf(stderr, "gtcoh: write-back MMAP_OFFSET failed: %s\n",
            strerror(errno));
    rc = EXIT_UNSUPPORTED;
    goto out;
  }
  uint32_t batch[BATCH_BYTES / 4];
  memset(batch, 0, sizeof batch);
  const uint64_t va_off = (uint64_t)m * MODE_VA_STEP;
  build_batch(batch, o->size, va_off);
  if (gem_write(fd, hb, batch, sizeof batch)) {
    fprintf(stderr, "gtcoh: writing the batch failed: %s\n", strerror(errno));
    rc = EXIT_UNSUPPORTED;
    goto out;
  }

  struct drm_i915_gem_exec_object2 obj[3];
  memset(obj, 0, sizeof obj);
  obj[0].handle = hs;
  obj[0].offset = SRC_VA + va_off;
  obj[0].flags = EXEC_OBJECT_PINNED | EXEC_OBJECT_SUPPORTS_48B_ADDRESS;
  obj[1].handle = hd;
  obj[1].offset = DST_VA + va_off;
  obj[1].flags =
      EXEC_OBJECT_PINNED | EXEC_OBJECT_SUPPORTS_48B_ADDRESS | EXEC_OBJECT_WRITE;
  obj[2].handle = hb;
  obj[2].offset = BATCH_VA + va_off;
  obj[2].flags = EXEC_OBJECT_PINNED | EXEC_OBJECT_SUPPORTS_48B_ADDRESS;
  struct drm_i915_gem_execbuffer2 eb;
  memset(&eb, 0, sizeof eb);
  eb.buffers_ptr = (uintptr_t)obj;
  eb.buffer_count = 3;
  eb.batch_len = BATCH_DWORDS * 4;
  eb.flags = I915_EXEC_BLT | I915_EXEC_NO_RELOC;

  volatile uint32_t *vs = src, *vd = dst;
  t0 = now_s();
  int printed = 0;
  for (uint64_t it = 1; it <= o->iters; it++) {
    if (now_s() - t0 > o->max_seconds) break;
    if (gt_reads_cpu) {
      /* HC-17: fresh source through the WB mapping; no set_domain, no
       * flush. */
      for (uint32_t i = 0; i < words; i++) vs[i] = pattern(it, i);
    } else {
      /* HG-5: the source goes through i915's CPU-write domain, so i915
       * makes it visible to the GT; this direction is not under test. */
      if (gem_set_domain(fd, hs, I915_GEM_DOMAIN_CPU, I915_GEM_DOMAIN_CPU)) {
        r->errors++;
        rc = EXIT_GPU;
        break;
      }
      for (uint32_t i = 0; i < words; i++) vs[i] = pattern(it, i);
      /* Warm the CPU cache with the destination's current content. */
      uint32_t sink = 0;
      for (uint32_t i = 0; i < words; i += 16) sink += vd[i];
      __asm__ volatile("" ::"r"(sink) : "memory");
    }
    __asm__ volatile("" ::: "memory");
    if (xioctl(fd, DRM_IOCTL_I915_GEM_EXECBUFFER2, &eb)) {
      fprintf(stderr, "gtcoh: %s: EXECBUFFER2 failed at iteration %" PRIu64
                      ": %s\n", mode_names[m], it, strerror(errno));
      r->errors++;
      rc = errno == ENODEV || errno == EINVAL ? EXIT_UNSUPPORTED : EXIT_GPU;
      break;
    }
    if (early) check_dst(o, m, vd, words, it, r, &printed);
    if (gem_wait(fd, hd, o->timeout_ns)) {
      fprintf(stderr, "gtcoh: %s: GEM_WAIT failed at iteration %" PRIu64
                      ": %s\n", mode_names[m], it, strerror(errno));
      r->errors++;
      rc = EXIT_GPU;
      break;
    }
    if (!early) {
      if (gt_reads_cpu) {
        /* HC-17 reads the destination through i915's CPU-read domain. */
        if (gem_set_domain(fd, hd, I915_GEM_DOMAIN_CPU, 0)) {
          r->errors++;
          rc = EXIT_GPU;
          break;
        }
      }
      __asm__ volatile("" ::: "memory");
      check_dst(o, m, vd, words, it, r, &printed);
    }
    r->iters = it;
  }
out:
  if (src) munmap(src, o->size);
  if (dst) munmap(dst, o->size);
  if (hb) gem_close(fd, hb);
  if (hd) gem_close(fd, hd);
  if (hs) gem_close(fd, hs);
  r->fatal = rc;
  const char *cn[] = {"none", "cached"};
  printf("gtcoh: mode=%s kind=%s dir=%s src_caching=%s dst_caching=%s "
         "stress=%s size=%u iters=%" PRIu64 " stale=%" PRIu64
         " other=%" PRIu64 " errors=%" PRIu64 " first_stale=%" PRId64
         " seconds=%.1f%s\n",
         mode_names[m], (m == M_HC17 || m == M_HG5) ? "soundness"
                                                    : "sensitivity",
         gt_reads_cpu ? "cpu-to-gt" : "gt-to-cpu", cn[src_caching & 1],
         cn[dst_caching & 1], o->stress ? "on" : "off", o->size, r->iters,
         r->stale, r->other, r->errors, r->first_stale, now_s() - t0,
         rc ? " (aborted)" : "");
  fflush(stdout);
  return rc;
}

int main(int argc, char **argv) {
  struct options o;
  if (parse_args(argc, argv, &o)) {
    usage(stderr);
    return EXIT_USAGE;
  }
  if (o.dry_run) {
    dry_run(&o);
    return EXIT_OK;
  }
  char path[64] = "";
  int fd = open_device(o.device, path, sizeof path);
  if (fd < 0) return -fd;

  int chipset = 0, has_llc = 0, softpin = 0, mmap_ver = 0;
  getparam(fd, I915_PARAM_CHIPSET_ID, &chipset);
  getparam(fd, I915_PARAM_HAS_LLC, &has_llc);
  getparam(fd, I915_PARAM_HAS_EXEC_SOFTPIN, &softpin);
  getparam(fd, I915_PARAM_MMAP_GTT_VERSION, &mmap_ver);
  printf("gtcoh: device=%s chipset=0x%04x has_llc=%d softpin=%d "
         "mmap_gtt_version=%d\n",
         path, chipset, has_llc, softpin, mmap_ver);
  if (!softpin) {
    fprintf(stderr, "gtcoh: the driver does not support softpinning\n");
    close(fd);
    return EXIT_UNSUPPORTED;
  }

  pthread_t th;
  int have_thread = 0;
  if (o.stress) {
    stress_stop = 0;
    size_t bytes = (size_t)o.stress_mib << 20;
    have_thread =
        pthread_create(&th, NULL, stress_main, (void *)(uintptr_t)bytes) == 0;
    if (!have_thread) fprintf(stderr, "gtcoh: cannot start stress thread\n");
  }

  int exit_code = EXIT_OK;
  for (int m = 0; m < M_COUNT; m++) {
    if (!o.modes[m]) continue;
    struct result r;
    int rc = run_mode(fd, &o, (enum mode_id)m, &r);
    if (rc && exit_code == EXIT_OK) exit_code = rc;
    if (rc == EXIT_GPU) break; /* the engine may have been reset; stop */
    if ((m == M_HC17 || m == M_HG5) && r.stale && exit_code == EXIT_OK)
      exit_code = EXIT_STALE;
  }

  if (have_thread) {
    stress_stop = 1;
    pthread_join(th, NULL);
  }
  close(fd);
  return exit_code;
}
