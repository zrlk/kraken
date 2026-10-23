# Sourced by Scc/Test/run.sh and Scc/Test/diff.sh: how arm binaries are run.
#
# Mode (option --arm-run MODE, or environment ARM_RUN; default qemu):
#   qemu    run under `qemu-aarch64 -cpu max` (functional check only: qemu
#           does not exhibit the weak-memory reorderings of real hardware).
#   native  run directly on the host; it must be an aarch64 Linux host whose
#           CPU has the features the emitted code relies on (see below),
#           otherwise the script stops with exit status 2.
#   auto    native if the host qualifies, otherwise qemu.
#
# scc's arm output is assembled with -march=armv8.4-a and relies on:
#   FEAT_LSE2 (Linux hwcap `uscat`, set by the kernel when
#     ID_AA64MMFR2_EL1.AT >= 1 on every CPU): an LDP/STP of two X registers
#     whose 16 bytes are 16-byte aligned is one single-copy-atomic access, on
#     Normal Inner/Outer Write-Back cacheable memory (all ordinary user
#     memory; not Device or non-cacheable mappings).  W-register pairs and
#     misaligned pairs are not 16-byte atomic.  This is the property assumed
#     by Kraken's `isaLSE2` model (Kraken/AArch64/EnvLSE2.lean).
#   FEAT_LSE (`atomics`): CAS, CASP, SWP.
#   FEAT_LRCPC (`lrcpc`): LDAPR.
# The hwcaps are what the CPU (or a hypervisor) reports: a hidden feature
# only makes `auto` fall back to qemu, but a falsely advertised FEAT_LSE2
# cannot be detected from user space.  All three are read from the
# `Features` line of /proc/cpuinfo (ARM_CPUINFO overrides the path, for
# testing this script).

ARM_RUN=${ARM_RUN:-qemu}

# Prints why the host cannot run arm binaries natively; status 0 if it can.
arm_native_why_not() {
  local m feats f
  m=$(uname -m)
  [ "$m" = aarch64 ] || { echo "host architecture is $m, not aarch64"; return 1; }
  [ "$(uname -s)" = Linux ] || { echo "host OS is $(uname -s), not Linux"; return 1; }
  feats=$(awk -F: '/^Features/ { print $2; exit }' "${ARM_CPUINFO:-/proc/cpuinfo}" 2>/dev/null)
  for f in uscat atomics lrcpc; do
    case " $feats " in
      *" $f "*) ;;
      *) echo "CPU lacks hwcap '$f' ($(case $f in uscat) echo FEAT_LSE2;; atomics) echo FEAT_LSE;; lrcpc) echo FEAT_LRCPC;; esac))"
         return 1 ;;
    esac
  done
  return 0
}

# Resolves ARM_RUN to qemu or native and announces the choice; exits 2 on a
# bad mode or when native is requested on a host that does not qualify.
arm_run_resolve() {
  local why
  case "$ARM_RUN" in
    qemu) ;;
    native)
      why=$(arm_native_why_not) || { echo "--arm-run native: $why" >&2; exit 2; } ;;
    auto)
      if why=$(arm_native_why_not); then ARM_RUN=native; else ARM_RUN=qemu; fi ;;
    *) echo "unknown --arm-run mode $ARM_RUN (available: qemu, native, auto)" >&2; exit 2 ;;
  esac
  if [ "$ARM_RUN" = native ]; then
    echo "arm runner: native ($(uname -m), FEAT_LSE2/LSE/LRCPC present)"
  else
    echo "arm runner: qemu-aarch64 -cpu max${why:+ (native unavailable: $why)}"
  fi
}

# Runs arm binary $1 with the resolved runner and a timeout (20 s native,
# 60 s under qemu, as for the x64 and qemu runs before).
arm_exec() {
  if [ "$ARM_RUN" = native ]; then timeout 20 "$1"
  else timeout 60 qemu-aarch64 -cpu max "$1"; fi
}
