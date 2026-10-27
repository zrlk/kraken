#!/usr/bin/env bash
# Certification after the link: compile a program with scc, link it as
# Scc/Test/run.sh does, read the layout the linker gave it from the ELF file,
# and check, in the kernel, the placement check at that layout and (with
# --instantiate) the compiler theorem at it.
#
# Usage: Scc/Test/certify.sh [--arch x64|arm] [--instantiate] [--elf EXE] [-v|--verbose] PROG.w
#
# First it builds what it needs (`lake build`: scc and the certificate
# modules, and with --instantiate the compiler theorem's module), printing
# one line per build; on a fresh checkout that is most of the package and
# takes long (the line says how long). The build output is appended to
# .lake/certify/ARCH/T/build.log; a failed build's verdict names it, after
# its last lines.
#
# -v, --verbose: print every command the script runs to standard error, before
# it runs, as a shell line to rerun by hand (`+ cd DIR && CMD ...`, absolute
# paths), and `# wrote PATH (...)` for each Lean file it generates (rerun with
# `lake env lean PATH` from the package root). Otherwise the same: outputs,
# verdict and exit status.
#
# Steps, in the work directory .lake/certify/ARCH/T/ (T = PROG's base name):
#   1. `scc --arch ARCH --cert T.cert.lean -o T.s PROG.w`; the certificate's
#      digests of the source and the text must be `sha256sum`'s.
#   2. Assemble and link T.s into T with run.sh's commands (x64: GNU `as`,
#      `ld -static`; arm: clang with lld), so that the executable certified
#      is the one run.sh runs. With --elf EXE, EXE is taken as the executable
#      instead (a file linked otherwise, or a damaged one for the tests).
#   3. The ELF layout reader (`Scc.Cert.Elf.elfParts`) on T, by evaluation,
#      for its refusal, if any, in a few seconds.
#   4. T.post.lean (with --instantiate its header comment, and a line of
#      output before the verdict, name the theorem's path, below): the
#      certificate without its decisions at the static link
#      (`prog_placeOK*`, `prog_cert_ready`), then the layout of T as a literal
#      (`scc_elf_layout%`, with the executable's SHA-256 checked by `#guard`),
#      `placeOKAt` at it decided component by component (`decide +kernel`) and,
#      with --instantiate, the compiler theorem at that layout
#      (`prog_correct_linked`, with `#print axioms`). The file is checked with
#      `lake env lean` in the Kraken package (`lake` from `$LAKE`, default
#      `lake`); its time and peak RssAnon are printed (`rssanon.sh`).
#   5. When T.post.lean does not check: the first component of `placeOKAt`
#      that fails at T's layout, by evaluation (untrusted, as placediag.sh).
#
# Verdicts (the last line of output, `certify: T (ARCH): VERDICT`) and exit
# status:
#   0  certified: the compiler theorem holds at the executable's layout
#      (--instantiate, and T.post.lean checks);
#   10 placement decided: acceptance and `placeOKAt` at the executable's
#      layout check, the theorem is not instantiated (no --instantiate);
#   3  not certifiable: outside the certified fragment (non-tail recursion:
#      no stack need table; or not `Scc.Lower.Accepted1`; on x64 with
#      --instantiate, `main`'s frame above 4096 bytes and not
#      `Scc.Lower.Accepted0`), or a component AN
#      of `placeOKAt` fails at the executable's layout;
#   1  failed: scc, the assembler, the linker or the reader fails (a damaged
#      executable), or T.post.lean does not check for another reason;
#   2  usage.
#
# The theorem instantiated: on arm `a64_scc_correctE_text_closedAt1`
# (fragment `Scc.Lower.Accepted1`, `prog_accepted1`). On x64
# `x64_scc_correctE_text_closedAt1` (`prog_accepted1`) when `main`'s frame is
# at most 4096 bytes (`Spike.Lib.LowerX64.MainFrame1Ok`: evaluated to choose,
# untrusted, then `prog_mainFrame1` by `decide +kernel`), else, for an
# `Scc.Lower.Accepted0` program, `x64_scc_correctE_text_closedAt`
# (`prog_accepted`). CERTIFY_X64_FRAGMENT=0 in the environment takes the
# latter for every `Accepted0` program (a test of that path: no `Accepted0`
# program found exceeds the bound; one with `maxAdds0` checked `+`s has a
# frame of 4064 bytes, evidence that the fallback is rarely taken, not a
# proof that it is never needed).
#
# hello1 (the registry of programs outside `Scc.Lower.Accepted1` with a
# proved theorem; it has one entry): when PROG.w is `Scc/Test/hello1.w` byte
# for byte and T.s is the text that theorem is about byte for byte
# (`Scc/Test/elf/hello1x64/hello1.s`, `Scc/Test/elf/hello1a64/hello1.s`, the
# checked-in certificate's `asm`), the theorem instantiated is
# `Spike.Lib.LowerX64.hello1_finalC_gen` (arm: `Spike.Lib.LowerA64.hello1_finalCA_gen`)
# at the executable's layout, with the stack witness
# `hello1_ok_witness_of_placeOKAt` (arm: `hello1_ok_witness_of_placeOKAtA`)
# there, so that its entry quantifier is not vacuous, and the code filling the
# executable's code region (`codeFills`, `e2eOk`). That theorem is about the
# checked-in program (`Spike.Test.Hello1MainSrc.hello1o`) and the checked-in
# certificate (`Spike.Test.Cert.X64Hello1Cert`, `Spike.Test.Cert.A64Hello1Cert`):
# T.post.lean imports them and never this run's certificate. Its parse premise
# `hpa` is checked by evaluation (`#guard`), its budget is `allocCells`
# (4194304 cells), and the `.text` bytes of the executable are not compared
# with the assembler's encoding of `asm`. Its build (`lake build
# Spike.Test.X64Hello1FinalC`, arm `Spike.Test.A64Hello1FinalCA`, with
# LEAN_NUM_THREADS=1) took, measured on a checkout with nothing under Spike
# built: x64 47 minutes (1323 jobs, peak RssAnon 4.0 GiB: leave 4.5 GiB free),
# then arm 31 more minutes (peak RssAnon 3.1 GiB; alone, at most the sum). Another program
# outside `Accepted1`, or hello1.w with another text, is not certifiable
# (exit 3: no proved theorem).
set -u

ARCH=x64; INST=0; ELF=""; SRC=""; VERBOSE=0
USAGE="usage: $0 [--arch x64|arm] [--instantiate] [--elf EXE] [-v|--verbose] PROG.w"
while [ $# -gt 0 ]; do
  case "$1" in
    --arch) ARCH="${2:-}"; shift 2 ;;
    --instantiate) INST=1; shift ;;
    --elf) ELF="${2:-}"; shift 2 ;;
    -v|--verbose) VERBOSE=1; shift ;;
    -*) echo "$USAGE" >&2; exit 2 ;;
    *) [ -z "$SRC" ] || { echo "$0: more than one program" >&2; exit 2; }; SRC="$1"; shift ;;
  esac
done
case "$ARCH" in
  x64) NS=Scc.Cert.PlaceOK.X64 ;;
  arm) NS=Scc.Cert.PlaceOK.A64 ;;
  *) echo "unknown arch $ARCH" >&2; exit 2 ;;
esac
[ -n "$SRC" ] && [ -f "$SRC" ] || { echo "$USAGE" >&2; exit 2; }
if [ -n "$ELF" ]; then [ -f "$ELF" ] || { echo "$0: no file $ELF" >&2; exit 2; }; ELF=$(cd "$(dirname "$ELF")" && pwd)/$(basename "$ELF"); fi

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
LAKE=${LAKE:-lake}
SCC="$ROOT/.lake/build/bin/scc"
T=$(basename "$SRC" .w)
REL=".lake/certify/$ARCH/$T"
WORK="$ROOT/$REL"
SRCABS=$(cd "$(dirname "$SRC")" && pwd)/$(basename "$SRC")

verdict() {  # status, text
  echo "certify: $T ($ARCH): $2"
  exit "$1"
}

# -v: the command about to run, in directory $1, as a shell line on stderr.
show() {
  [ $VERBOSE = 1 ] || return 0
  local d=$1; shift
  { printf '+ cd %q &&' "$d"; printf ' %q' "$@"; echo; } >&2
}
# -v: a Lean file the script wrote ($1) and what it is for ($2).
wrote() { [ $VERBOSE = 1 ] && echo "# wrote $1 ($2)" >&2; return 0; }

rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK" || exit 1
show "$ROOT" mkdir -p "$WORK"
BLOG="$WORK/build.log"
BENV=""
# Build targets $3... ($1: what, $2: the time a fresh checkout takes); on
# failure the verdict names the log, after its last lines.
build() {
  local what=$1 time=$2; shift 2
  echo "certify: building $what (lake build $*; a first run on a fresh checkout takes $time); log: $BLOG"
  show "$ROOT" ${BENV:+env $BENV} $LAKE build "$@"
  (cd "$ROOT" && ${BENV:+env $BENV} $LAKE build "$@") >>"$BLOG" 2>&1 && return 0
  tail -n 20 "$BLOG"
  return 1
}

if [ "$ARCH" = x64 ]; then CERT_MODS="Scc.Cert.X64 Scc.Cert.OutStageX64 Scc.Cert.E2EX64"
else CERT_MODS="Scc.Cert.Arm Scc.Cert.OutStageA64 Scc.Cert.E2EA64"; fi
build "scc and the certificate modules" "about 15 minutes on 64 cores" scc scc_x64 scc_arm Scc.Cert.Elf Scc.Cert.SrcTerm $CERT_MODS \
  || verdict 1 "failed: lake build scc (log: $BLOG)"
# (hello1.w builds its own theorem's module instead, below.)
if [ $INST = 1 ] && ! cmp -s "$SRCABS" "$ROOT/Scc/Test/hello1.w"; then
  if [ "$ARCH" = x64 ]; then THM_MOD=Spike.Lib.LowerX64.Correct1; else THM_MOD=Spike.Lib.LowerA64.Correct1; fi
  build "the compiler theorem" "about 3 minutes" "$THM_MOD" || verdict 1 "failed: lake build $THM_MOD (log: $BLOG)"
fi
show "$WORK" cp "$SRCABS" "$T.w"
cp "$SRCABS" "$T.w"

# 1. Compile, with the certificate.
show "$WORK" "$SCC" --arch "$ARCH" --cert "$T.cert.lean" -o "$T.s" "$T.w"
"$SCC" --arch "$ARCH" --cert "$T.cert.lean" -o "$T.s" "$T.w" >"$T.scc.out" 2>"$T.scc.err" \
  || verdict 1 "failed: scc: $(head -c 2000 "$T.scc.err")"
OUTSIDE="-- outside the certified fragment: no stack need table (non-tail recursion)"
if grep -qxF -- "$OUTSIDE" "$T.cert.lean"; then
  verdict 3 "not certifiable: outside the certified fragment (no stack need table: non-tail recursion)"
fi
show "$WORK" sha256sum "$T.w" "$T.s"
hs=$(sha256sum "$T.w" | cut -d' ' -f1); ha=$(sha256sum "$T.s" | cut -d' ' -f1)
if [ "$(grep -c "^-- SHA-256 (UTF-8): \($hs\|$ha\)\$" "$T.cert.lean")" != 2 ]; then
  verdict 1 "failed: the certificate's digests differ from sha256sum"
fi
# The fragment: `Scc.Lower.Accepted1` (`prog_accepted1`, which every
# `Accepted0` program has: `Scc.Lower.accepted1_of_accepted0`). On x64 the
# theorem over it also needs `main`'s frame within 4096 bytes
# (`MainFrame1Ok`); without it an `Accepted0` program takes the theorem over
# `Accepted0` (`prog_accepted`), which needs no such bound.
ACC="prog_accepted1"; ACCP="Scc.Lower.Accepted1"; IMMS="Scc.Lower.imms1Of prog_src"; HFR=""
PATHN="closedAt1"
HELLO1=0
if ! grep -q "^theorem $ACC : $ACCP prog_src = true" "$T.cert.lean"; then
  # The registry (see the header): `Scc/Test/hello1.w`, byte for byte.
  show "$WORK" cmp "$T.w" "$ROOT/Scc/Test/hello1.w"
  if cmp -s "$T.w" "$ROOT/Scc/Test/hello1.w"; then
    HELLO1=1
  else
    # `Scc.Lower.Accepted2` by evaluation, for the message only (untrusted).
    build "the fragment check" "seconds" Scc.Frontend Scc.Lower.Spec2 \
      || verdict 1 "failed: lake build Scc.Lower.Spec2 (log: $BLOG)"
    cat >"$T.acc2.lean" <<EOF
import Scc.Frontend
import Scc.Lower.Spec2
#eval show IO Unit from do
  match Scc.Frontend.run (← IO.FS.readFile "$REL/$T.w") with
  | .ok c => IO.println s!"certify-acc2: {Scc.Lower.Accepted2 c.prog}"
  | .error _ => IO.println "certify-acc2: false"
EOF
    wrote "$WORK/$T.acc2.lean" "Scc.Lower.Accepted2 of the program, by evaluation: prints certify-acc2: true or false"
    show "$ROOT" "$LAKE" env lean "$WORK/$T.acc2.lean"
    r=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.acc2.lean" 2>&1 | sed -n 's/^certify-acc2: //p' | head -n 1)
    if [ "$r" = true ]; then
      verdict 3 "not certifiable: outside the certified fragment (Accepted2 programs other than \
Scc/Test/hello1.w have no proved theorem: no proved theorem for this program/text)"
    fi
    verdict 3 "not certifiable: outside the certified fragment (not $ACCP; no proved theorem for this program/text)"
  fi
fi
if [ $HELLO1 = 1 ]; then
  # hello1's theorem is about the checked-in text: T.s must be it, byte for byte.
  if [ "$ARCH" = x64 ]; then H1ISA=x64; else H1ISA=a64; fi
  H1S="Scc/Test/elf/hello1$H1ISA/hello1.s"
  show "$WORK" cmp "$T.s" "$ROOT/$H1S"
  cmp -s "$T.s" "$ROOT/$H1S" \
    || verdict 3 "not certifiable: no proved theorem for this program/text \
($T.s is not $H1S, the text of hello1's theorem)"
  if [ "$ARCH" = x64 ]; then
    H1CERT=Spike.Test.Cert.X64Hello1Cert; H1MOD=Spike.Test.X64Hello1FinalC
    H1COLD="47 minutes; 4.5 GiB free"
    H1GEN=Spike.Lib.LowerX64.hello1_finalC_gen; H1WIT=Spike.Lib.LowerX64.hello1_ok_witness_of_placeOKAt
    H1EQ=Spike.Lib.LowerX64.hello1_out_eq; H1LAY=Spike.Lib.LowerX64.lay2
    H1HPA="Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs"
  else
    H1CERT=Spike.Test.Cert.A64Hello1Cert; H1MOD=Spike.Test.A64Hello1FinalCA
    H1COLD="31 minutes after x64's, at most 78 alone"
    H1GEN=Spike.Lib.LowerA64.hello1_finalCA_gen; H1WIT=Spike.Lib.LowerA64.hello1_ok_witness_of_placeOKAtA
    H1EQ=Spike.Lib.LowerA64.hello1_out_eqA; H1LAY=Spike.Lib.LowerA64.lay2
    H1HPA="Scc.Cert.Link.A64.parsesTo asm outLit.prog outLit.secs"
  fi
  if [ $INST = 1 ]; then
    BENV="LEAN_NUM_THREADS=1"
    build "hello1's theorem" "$H1COLD" "$H1MOD" || verdict 1 "failed: lake build $H1MOD (log: $BLOG)"
    BENV=""
  else
    build "hello1's certificate" "about a minute" "$H1CERT" || verdict 1 "failed: lake build $H1CERT (log: $BLOG)"
  fi
  PATHN="hello1 (registry): ${H1GEN##*.}"
fi
if [ "$ARCH" = x64 ] && [ $INST = 1 ] && [ $HELLO1 = 0 ]; then
  # `MainFrame1Ok` by evaluation, to choose the theorem (untrusted: the
  # kernel decides it below, `prog_mainFrame1`).
  {
    echo "import Scc.Frontend"
    echo "import Spike.Lib.LowerX64.MainCode1"
    grep '^def config : Scc.Config :=' "$T.cert.lean"
    cat <<EOF
#eval show IO Unit from do
  match Scc.Frontend.run (← IO.FS.readFile "$REL/$T.w") with
  | .ok c => match c.prog with
    | [d] => IO.println s!"certify-frame1: {Spike.Lib.LowerX64.MainFrame1Ok config d}"
    | _ => IO.println "certify-frame1: false"
  | .error _ => IO.println "certify-frame1: false"
EOF
  } >"$T.frame1.lean"
  wrote "$WORK/$T.frame1.lean" "MainFrame1Ok of main, by evaluation: prints certify-frame1: true or false"
  show "$ROOT" "$LAKE" env lean "$WORK/$T.frame1.lean"
  r=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.frame1.lean" 2>&1 | sed -n 's/^certify-frame1: //p' | head -n 1)
  [ "${CERTIFY_X64_FRAGMENT:-}" = 0 ] && [ "$r" = true ] && r=false
  case "$r" in
    true) HFR=" prog_mainFrame1"; PATHN="closedAt1+MainFrame1Ok" ;;
    false)
      if grep -q "^theorem prog_accepted : Scc.Lower.Accepted0 prog_src = true" "$T.cert.lean"; then
        ACC="prog_accepted"; ACCP="Scc.Lower.Accepted0"; IMMS="Spike.Lib.LowerNode.immsOf main"
        PATHN="closedAt fallback"
      else
        verdict 3 "not certifiable: main's frame exceeds 4096 bytes (not MainFrame1Ok) and not Scc.Lower.Accepted0"
      fi ;;
    *) verdict 1 "failed: MainFrame1Ok could not be evaluated" ;;
  esac
fi
# The theorem's path, on stdout and in T.post.lean's header (chosen by
# evaluation, untrusted: the kernel checks the theorem instantiated).
[ $INST = 1 ] && echo "certify: $T ($ARCH): theorem: $PATHN"

# 2. Assemble and link (run.sh's commands), or take the given executable.
if [ -n "$ELF" ]; then
  show "$WORK" cp "$ELF" "$T"
  cp "$ELF" "$T"
elif [ "$ARCH" = x64 ]; then
  show "$WORK" as -o "$T.o" "$T.s"; show "$WORK" ld -static -o "$T" "$T.o"
  { as -o "$T.o" "$T.s" && ld -static -o "$T" "$T.o"; } 2>"$T.link.err" \
    || verdict 1 "failed: assemble/link: $(head -c 2000 "$T.link.err")"
else
  show "$WORK" clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o "$T" "$T.s"
  clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o "$T" "$T.s" 2>"$T.link.err" \
    || verdict 1 "failed: assemble/link: $(head -c 2000 "$T.link.err")"
fi
show "$WORK" sha256sum "$T"
he=$(sha256sum "$T" | cut -d' ' -f1)

# 3. The reader, by evaluation.
cat >"$T.elf.lean" <<EOF
import Scc.Cert.Elf
#eval show IO Unit from do
  match Scc.Cert.Elf.elfParts (← IO.FS.readBinFile "$REL/$T") with
  | .error e => IO.println s!"certify-elf: refused: {e}"
  | .ok _ => IO.println "certify-elf: ok"
EOF
wrote "$WORK/$T.elf.lean" "the ELF reader on $T, by evaluation: prints certify-elf: ok or the refusal"
show "$ROOT" "$LAKE" env lean "$WORK/$T.elf.lean"
r=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.elf.lean" 2>&1 | sed -n 's/^certify-elf: //p' | head -n 1)
case "$r" in
  ok) ;;
  refused:*) verdict 1 "failed: the ELF reader refuses $T: ${r#refused: }" ;;
  *) verdict 1 "failed: the ELF reader could not be run" ;;
esac

# 4. The certificate after the link.
if [ "$ARCH" = x64 ]; then
  HPA="Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs"; TEXT="⟨asm, sizes, labelOffs⟩"
  CORRECTE="Scc.Sem.X64.CorrectE"; THM="Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt"
  [ "$ACC" = prog_accepted1 ] && THM="Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt1"
  CODEEND="Scc.Sem.X64.codeEnd"; E2E="Scc.Cert.E2E.X64"; E2E_MOD="Scc.Cert.E2EX64"
else
  CODEEND="Scc.Sem.A64.codeEnd"; E2E="Scc.Cert.E2E.A64"; E2E_MOD="Scc.Cert.E2EA64"
  HPA="Scc.Cert.Link.A64.parsesTo asm out.prog out.secs"; TEXT="asm"
  CORRECTE="Scc.Sem.A64.CorrectE"; THM="Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt1"
fi
L="⟨elf.1⟩"
# On both ISAs A9 is by its keyed form and A12 (the code of every user
# function) by its two keyed parts, each its own declaration
# (`Scc/Cert/A12StageA64.lean`, `Scc/Cert/A12StageX64.lean`: the kernel's
# peak is the largest of them).
A9PF="
  $NS.a9_of_fast (by decide +kernel)"
A2="a2"; A2PF="h1.1.1.2"
if [ "$ARCH" = arm ]; then
  # A2 by its keyed form (`a2fast`, `Scc/Cert/A2StageA64.lean`).
  A2="a2fast"; A2PF="($NS.a2_of_fast h1.1.1.2)"
fi
A12THM="
/-- A12's code part of \`outLit\` (kernel-checked). -/
theorem prog_placeOKAt_12c : $NS.a12code outLit = true := by
  decide +kernel

/-- A12's phase part of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_12p : $NS.a12ph outLit $L = true := by
  decide +kernel

/-- A12 of \`outLit\` at the executable's layout. -/
theorem prog_placeOKAt_12 : $NS.a12 outLit $L = true :=
  $NS.a12_of_split prog_placeOKAt_12c prog_placeOKAt_12p
"
A12ARG=" prog_placeOKAt_12"
CODEFILLS="(by decide +kernel)"
[ $HELLO1 = 1 ] && CODEFILLS="prog_codeFills"
{
  echo "import Scc.Cert.Elf"
  echo "import $E2E_MOD"
  if [ $HELLO1 = 1 ]; then
    if [ $INST = 1 ]; then echo "import $H1MOD"; else echo "import $H1CERT"; fi
    cat <<EOF

-- certify.sh: theorem path: $PATHN. The theorem is about the checked-in program and
-- certificate ($H1CERT, imported). This run's certificate is not pasted here, on purpose:
-- its \`sizes\` and \`labelOffs\` are not the theorem's (T.s is the theorem's text: \`cmp\`).

namespace SccCertificate

-- This run's text is the theorem's \`asm\`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "$REL/$T.s") == asm)

EOF
  elif [ $INST = 1 ]; then
    echo "import $THM_MOD"
    echo
    echo "-- certify.sh: theorem path: $PATHN (on x64 chosen by evaluating MainFrame1Ok,"
    echo "-- untrusted; the kernel checks the theorem instantiated, \`prog_correct_linked\`)."
  fi
  # The certificate up to its decisions at the static link (they are not
  # needed: the decisions below are at the executable's layout).
  [ $HELLO1 = 1 ] || sed -e '/^\/-- A1 of `outLit`/,$d' "$T.cert.lean"
  cat <<EOF
/-! ## After the link

The executable \`$T\` that the linker wrote from \`asm\` (\`Scc/Test/certify.sh\`),
its layout read from its ELF file (\`Scc.Cert.Elf\`, fail closed), and the
placement check at that layout (\`placeOKAt\`) in place of the static link's.
-/

-- The executable's SHA-256: $he
/-- The layout of the executable and its SHA-256 (\`scc_elf_layout%\`: read at
elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "$REL/$T"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "$he"
EOF
  if [ $HELLO1 = 1 ]; then cat <<EOF

/-- \`outLit\`'s code fills the executable's code region (kernel-checked). -/
theorem prog_codeFills : $E2E.codeFills outLit elf.1 = true := by
  decide +kernel
EOF
  fi
  cat <<EOF

/-- The code the canonical loader lays out from \`outLit\` ends where the
executable's code region does (kernel-checked). -/
theorem prog_codeEnd : $CODEEND elf.1.code.lo outLit.prog = elf.1.code.lo + elf.1.code.size :=
  $E2E.codeEnd_eq_of_codeFills (o := outLit) (Λ := elf.1) $CODEFILLS

/-- A1, A2, A4 and A7 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_1 : ($NS.a1 outLit $L && $NS.$A2 outLit $L &&
    $NS.a4 placeCfg outLit $L && $NS.a7 outLit $L) = true := by
  decide +kernel

/-- A3 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_3 : $NS.a3 outLit $L = true :=
  $NS.a3_of_partsAt (by decide +kernel) (by decide +kernel)

/-- A5 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_5 : $NS.a5 outLit $L = true := by
  decide +kernel

/-- A6 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_6 : $NS.a6 outLit $L = true :=
  $NS.a6_of_partsAt (by decide +kernel) (by decide +kernel)

/-- A8 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_8 : $NS.a8 outLit $L = true := by
  decide +kernel

/-- A11 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_11 : $NS.a11 outLit $L = true := by
  decide +kernel
$A12THM
/-- A9 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_9 : $NS.a9 outLit $L = true :=$A9PF

/-- **\`placeOKAt\` of \`scc\`'s output at the executable's layout**, from its
components (\`placeOKAt_of\`). -/
theorem prog_placeOKAt : $NS.placeOKAt placeCfg elf.1 out = true := by
  have h1 := prog_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact $NS.placeOKAt_of
    h1.1.1.1 $A2PF prog_placeOKAt_3 h1.1.2 prog_placeOKAt_5 prog_placeOKAt_6 h1.2 prog_placeOKAt_8
    prog_placeOKAt_9 prog_placeOKAt_11$A12ARG
EOF
  if [ $HELLO1 = 1 ]; then cat <<EOF

/-- **The end-to-end guard at the executable's layout**: \`placeOKAt\` and the code
filling the executable's code region. -/
theorem prog_e2eOk : $E2E.e2eOk placeCfg elf.1 outLit = true := by
  have h := prog_placeOKAt
  rw [out_eq] at h
  simp only [$E2E.e2eOk, h, prog_codeFills, Bool.and_self]
EOF
    if [ $INST = 1 ]; then cat <<EOF

/-- **The entry quantifier is not vacuous** at the executable's layout: the 64 KiB
stack at \`2 ^ 32\` is admissible (\`${H1WIT##*.}\`). -/
theorem prog_ok_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩ ($H1LAY elf.1 Spike.Test.Hello1MainSrc.hello1o) :=
  $H1WIT elf.1 ($H1EQ ▸ prog_placeOKAt)

-- \`hpa\`, by compiled evaluation: the theorem's parse premise (the trust boundary).
#guard $H1HPA

/-- **hello1's theorem at the executable's layout** (\`${H1GEN##*.}\`): \`asm\` is
correct at every admissible entry state, at the layout read from the executable,
for every memory model and every budget of \`allocCells\` cells, given the loader's
parse of \`asm\` (\`hpa\`, the \`#guard\` above). -/
theorem prog_correct_linked
    (hpa : $H1HPA = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    $CORRECTE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o)
        Spike.Test.Hello1MainSrc.hello1o)
      ($H1LAY elf.1 Spike.Test.Hello1MainSrc.hello1o) B $TEXT :=
  $H1GEN elf.1 ($H1EQ ▸ prog_placeOKAt) hpa hB

/--
info: 'SccCertificate.prog_correct_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prog_correct_linked

/--
info: 'SccCertificate.prog_ok_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prog_ok_witness
EOF
    fi
  else cat <<EOF

/-- **Acceptance and placement at the executable's layout.** -/
theorem prog_linked_ready : $ACCP prog_src = true ∧ $NS.placeOKAt placeCfg elf.1 out = true :=
  ⟨$ACC, prog_placeOKAt⟩
EOF
  fi
  if [ $INST = 1 ] && [ $HELLO1 = 0 ]; then cat <<EOF

/-- \`prog_src\`'s one declaration. -/
abbrev main : CoreTerm.Decl := prog_src.head (by decide)
EOF
    if [ -n "$HFR" ]; then cat <<EOF

/-- \`main\`'s frame is at most 4096 bytes, the reach of the stack check's
probe (\`Spike.Lib.LowerX64.MainFrame1Ok\`; kernel-checked). -/
theorem prog_mainFrame1 : Spike.Lib.LowerX64.MainFrame1Ok config main = true := by
  decide +kernel
EOF
    fi
    cat <<EOF

/-- **The compiler theorem at the executable's layout**: \`asm\` is correct
at every admissible entry state, at the layout read from the executable
(with the lowering's immediates), for every budget and memory model, given the
loader's parse of \`asm\` (\`hpa\`, the \`#guard\` above: the trust boundary). -/
theorem prog_correct_linked (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : $HPA = true) :
    $CORRECTE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { elf.1 with static := fun _ => none, imms := $IMMS } B $TEXT :=
  $THM (cfg := config) (pcfg := placeCfg) elf.1 $ACC prog_placeOKAt$HFR hpa

/--
info: 'SccCertificate.prog_correct_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prog_correct_linked
EOF
  fi
  echo
  echo "end SccCertificate"
} >"$T.post.lean"
if [ $INST = 1 ]; then
  wrote "$WORK/$T.post.lean" "the certificate at the executable's layout: placeOKAt and the compiler theorem"
else wrote "$WORK/$T.post.lean" "the certificate at the executable's layout: placeOKAt"; fi

rm -f post.rss
show "$ROOT" "$LAKE" env lean "$WORK/$T.post.lean"
if (cd "$ROOT" && "$ROOT/Scc/Test/rssanon.sh" "$WORK/post.rss" "$LAKE" env lean "$WORK/$T.post.lean") \
    >"$T.post.out" 2>&1; then
  secs=""; ra=""; [ -f post.rss ] && IFS=: read -r secs ra <post.rss
  m=""; [ -n "$ra" ] && m=", $((ra / 1024)) MB RssAnon peak"; [ -n "$secs" ] && m=" (${secs} s$m)"
  if [ $INST = 1 ] && [ $HELLO1 = 1 ]; then
    if [ -n "$ELF" ]; then X="the executable $ELF (--elf)"; else X="the executable $REL/$T (run.sh's link)"; fi
    verdict 0 "certified$m: $T.post.lean: ${H1GEN##*.} at the layout of $X, hello1 only \
(registry: Scc/Test/hello1.w and $H1S byte for byte); hpa by evaluation; budget hB: 4194304 cells \
(allocCells); the .text bytes are not compared with the encoding of asm"
  fi
  if [ $INST = 1 ]; then verdict 0 "certified$m: $T.post.lean"
  else verdict 10 "placement decided$m (not certified: the theorem is not instantiated; --instantiate): $T.post.lean"; fi
fi

# 5. It does not check: is it `placeOKAt` that fails, and at which component?
{
  echo "import Scc.Cert.Elf"
  if [ $HELLO1 = 1 ]; then echo "import $H1CERT"; echo; echo "namespace SccCertificate"; echo
    echo "#eval do IO.println s!\"certify-text: {(← IO.FS.readFile \"$REL/$T.s\") == asm}\""; else
  sed -e '/^\/-- `out` as a literal/,$d' "$T.cert.lean" | awk '
    function flush() { if (nd) printf "%s", doc; doc = ""; nd = 0 }
    skip && /^[ \t]/ { next }
    { skip = 0 }
    /^theorem / { doc = ""; nd = 0; skip = 1; next }
    indoc { doc = doc $0 "\n"; if ($0 ~ /-\/[ \t]*$/) indoc = 0; next }
    /^\/--/ { flush(); doc = $0 "\n"; nd = 1; if ($0 !~ /-\/[ \t]*$/) indoc = 1; next }
    { flush(); print }
    END { flush() }'
  fi
  cat <<EOF
def elf : Scc.Sem.Layout × String := scc_elf_layout% "$REL/$T"
#eval IO.println (match Scc.Cert.PlaceOK.Checks.firstFail ($NS.checks placeCfg) (fun _ => $L) out with
  | some n => s!"certify-diag: a{n}"
  | none => "certify-diag: none")

end SccCertificate
EOF
} >"$T.diag.lean"
wrote "$WORK/$T.diag.lean" "the first component of placeOKAt that fails, by evaluation: prints certify-diag: aN"
show "$ROOT" "$LAKE" env lean "$WORK/$T.diag.lean"
dout=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.diag.lean" 2>&1)
an=$(printf '%s\n' "$dout" | sed -n 's/^certify-diag: //p' | head -n 1)
if [ $HELLO1 = 1 ] && [ "$(printf '%s\n' "$dout" | sed -n 's/^certify-text: //p' | head -n 1)" != true ]; then
  verdict 3 "not certifiable: no proved theorem for this program/text ($T.s is not the checked-in asm)"
fi
case "$an" in
  a[0-9]*) verdict 3 "not certifiable: placeOKAt fails at the executable's layout (component ${an^^}; diagnostic by evaluation)" ;;
  *) verdict 1 "failed: $T.post.lean does not check (placeOKAt: ${an:-?}): $(grep -m1 -A3 'error' "$T.post.out" | head -c 2000)" ;;
esac
