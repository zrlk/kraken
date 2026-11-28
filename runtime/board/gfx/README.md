# Graphics board experiment kit

Experiments on the board's integrated GPU (Intel N200, ADL-N graphics, PCI
8086:46d0 at 00:02.0) under the stock Linux i915 driver. They test whether the
board's GT is coherent with the CPU caches in both directions, record the
firmware, engine, IOMMU, CPU and PCIe facts the coherence model depends on,
and compare GuC submission with execlists.

Files:

| File | What it is |
|---|---|
| `facts.sh` | read-only fact collection (shell) |
| `gtcoh.c` | the coherence test, an ordinary DRM client of i915 (C) |
| `run_all.sh` | runs both, and the read-only NIC facts of `../nic/facts.sh` (see `../nic/README.md`), in a safe order and writes `gfx-board-<date>.tar.gz` |
| `Makefile` | builds `gtcoh` (dynamic or static) |

## What each experiment shows

Every experiment has an id from the hardware experiment register (not
shipped). A
*soundness* experiment checks that an outcome the model forbids is never seen;
a *sensitivity* experiment checks that a weak outcome the model allows really
occurs on this setup. A soundness run counts as evidence only if its
sensitivity partner, on the same board and kernel, has fired at least once.

| Id | Claim | Kind | Where |
|---|---|---|---|
| HC-17 | The GT (copy engine) snoops CPU caches through the shared LLC: CPU stores to a write-back mapping of an LLC-cached object, with no flush, are seen by a following blit. | soundness | `gtcoh --mode hc17` |
| HC-17 partner | With the source object's caching set to NONE, the same blit can read stale memory. | sensitivity | `gtcoh --mode hc17-partner` |
| HG-5 | GT writes to an LLC-cached object are seen by CPU write-back reads after the wait, even when the CPU had the old data cached. | soundness | `gtcoh --mode hg5` |
| HG-5 partner | With the destination's caching set to NONE, the CPU can read its stale cached copy. | sensitivity | `gtcoh --mode hg5-partner` |
| checker | Reading the destination right after submitting, before the blit can have finished, reports stale words: the check can see a stale result. On a shared-LLC GPU (has_llc=1) the GT snoops the CPU caches even with caching NONE (i915, `i915_gem_object_types.h`), so the two partners above cannot fire; this mode is then the sensitivity check of the checker itself. | sensitivity | `gtcoh --mode checker` |
| HG-1 | With `i915.enable_guc=0` the GT runs on execlists with no GuC/HuC loaded, and copy-engine blits complete with correct data. | fact | reboot, then `run_all.sh` again |
| HG-2 | Which engines the N200 exposes (RCS0, BCS0, VCS*, VECS0). | fact | `facts/engines.txt`, `facts/debugfs-engines.txt` |
| HC-2 | VT-d ECAP of each unit; expected dmar0 SC=0, C=0 and dmar1 SC=1, C=0. | fact | `facts/iommu.txt` |
| HC-6 | Cache line size 64 and clflush, clflushopt and clwb present. | fact | `facts/cpu-cache.txt` |
| (facts) | GuC/HuC/DMC versions, submission mode, has_llc, PCIe Device Control of 00:02.0 and the Realtek NICs, kernel command line. | fact | `facts/summary.txt`, `facts/debugfs-*.txt`, `facts/pcie-devctl.txt`, `facts/cmdline.txt` |

### How gtcoh tests HC-17 and HG-5

Each iteration submits one batch to the copy engine: an `XY_FAST_COPY_BLT`
of the whole object (64 KiB by default, 32 bpp, linear, 4096-byte rows)
followed by `MI_BATCH_BUFFER_END`. The batch, source and destination are
softpinned at fixed 48-bit addresses in the client's own PPGTT (no
relocations). After each submission gtcoh waits on the destination with a
bounded GEM wait, then checks every dword. Each iteration writes a new
pattern, so a word that still holds the previous iteration's value is
counted as *stale*; any other wrong value is counted as *other*.

- **hc17**: the source is `I915_CACHING_CACHED`; the CPU writes the pattern
  through a write-back mapping (`I915_GEM_MMAP_OFFSET` with
  `I915_MMAP_OFFSET_WB`) with no set_domain call and no flush, then submits.
  The destination is read through i915's CPU read domain (set_domain), so
  this mode tests only the CPU-to-GT direction.
- **hg5**: before submitting, the CPU reads the destination through its
  write-back mapping, so the old data is in the CPU cache. The source is
  prepared through i915's CPU write domain (i915 makes it visible to the GT).
  After the wait the CPU reads the destination through the same mapping with
  no set_domain call, so this mode tests only the GT-to-CPU direction.
- **partners**: the same with the object under test set to
  `I915_CACHING_NONE`.
- **--stress**: a second thread streams through a 64 MiB buffer (larger than
  the 6 MiB LLC) during the run, to evict lines and vary timing.

**Inconclusive results.** If a partner never reports a stale word, the
matching soundness run shows nothing: the experiment could not have detected
a missing snoop. This can happen for reasons unrelated to the claim. i915
does its own cache maintenance: it may flush CPU caches for an object that is
not coherent when the object is submitted or when its caching changes, and on
LLC platforms it treats uncached objects as coherent for CPU reads. Also, the
time between the CPU store and the GT read (an ioctl, scheduling, the
submission path) gives the CPU caches many chances to write the line back on
their own. A partner that fires shows that the setup can see a stale result,
which is what gives a clean soundness run its weight.

### HG-1: GuC submission versus execlists

The board's kernel enables GuC submission by default (dmesg reports
`GuC submission enabled` and the `tgl_guc_70.bin` firmware). HG-1 asks whether
the GT also works with no GuC/HuC firmware at all. The kit never changes boot
parameters; do this by hand:

1. Run `run_all.sh` once with the default boot (GuC).
2. Reboot. In the GRUB menu of the live image, highlight the entry, press
   `e`, append ` i915.enable_guc=0` to the line that starts with `linux`, and
   press F10 (or Ctrl-X) to boot. The parameter lasts for this boot only.
3. Run `run_all.sh` again. `facts/summary.txt` records `enable_guc=0` and
   whether dmesg reports GuC submission; `gtcoh.txt` shows whether the blits
   complete with correct data.

i915 marks `enable_guc` as an unsafe parameter and taints the kernel when it
is set; that is expected. If i915 fails to bind with it, the facts still
record the dmesg output; reboot without the parameter.

## Building

On the board (if the image has gcc and `linux-libc-dev`):

    make

On another x86-64 Debian or Ubuntu machine, build a static binary and copy
`gtcoh` with the scripts to the board (for example on a USB stick):

    sudo apt install gcc make linux-libc-dev   # if missing
    make static

The build uses only the system uapi headers (`/usr/include/drm/i915_drm.h`)
and libc; it is warning-free with `-Wall -Wextra`.

## Running

As root, from a writable directory (the live image's home or /tmp):

    sudo ./run_all.sh            # full run: 10^5 iterations per mode
    sudo ./run_all.sh --quick    # 10^3 iterations, to check the setup first

`run_all.sh` collects the graphics facts and the NIC facts, prints the gtcoh dry run, runs the four
modes, runs them again with `--stress`, saves the kernel log lines after the
GPU work, and writes `gfx-board-<date>.tar.gz` in the current directory.
Each gtcoh mode stops after 600 s (60 s with `--quick`) and each GEM wait
after 5 s. The full run normally takes a few minutes.

gtcoh alone:

    ./gtcoh --help
    ./gtcoh --dry-run                     # print the batch; no device needed
    sudo ./gtcoh --mode hc17,hc17-partner --iters 100000 --stress

Exit codes: 0 all modes ran and no soundness mode saw stale data; 1 usage;
2 no i915 device; 3 permission denied; 4 the driver refused a needed feature
(softpin, set_caching or the write-back mapping); 5 GPU submission error or
wait timeout (gtcoh stops submitting); 6 stale data in a soundness mode.

## Expected output

`gtcoh.txt` has one header line and one line per mode, for example:

    gtcoh: device=/dev/dri/renderD128 chipset=0x46d0 has_llc=1 softpin=1 mmap_gtt_version=4
    gtcoh: mode=hc17 kind=soundness dir=cpu-to-gt src_caching=cached dst_caching=cached stress=off size=65536 iters=100000 stale=0 other=0 errors=0 first_stale=-1 seconds=...

`iters` is the number of iterations completed, `stale` the number of
iterations with at least one stale word, `other` those with any other wrong
word, and `errors` failed ioctls. For the claims to hold, the soundness modes
show `stale=0 other=0 errors=0`; the partners show `stale` > 0 if the setup is
sensitive. Any `other` > 0 or `errors` > 0 is worth a look at `dmesg-gfx-after.txt`.

## What to send back

The single file `gfx-board-<date>.tar.gz` from each run (one with the default
boot, one with `i915.enable_guc=0`). It contains the facts and nic directories, the
gtcoh output with and without stress, the dry run, the run log and the kernel
log lines after the run. It contains the full dmesg and lspci output of the
board and nothing else from the system.

## Safety

- `facts.sh` only reads: files under /proc, /sys and debugfs, `dmesg`,
  `lspci`. It changes no setting and loads or unloads no module.
- gtcoh is an ordinary DRM client: it uses the documented i915 ioctls on its
  own buffer objects, as any graphics program does. It touches no register,
  does not reload the driver and does not use the display.
- The GPU work is bounded: a fixed number of iterations, a time limit per
  mode, a 5 s bound on each wait, and an outer timeout in `run_all.sh`.
- If the GPU hangs on a batch, i915 detects it and resets the engine (or the
  GT); gtcoh's wait times out, it reports the error, stops submitting and
  exits with code 5. The display may flicker during a reset.
- No data on disk is touched: the kit writes only its own output directory
  and tarball in the current directory.
