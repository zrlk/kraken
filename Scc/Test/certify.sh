#!/usr/bin/env bash
# Certification after the link: compile a program with scc, link it as
# Scc/Test/run.sh does, read the layout the linker gave it from the ELF file,
# and check, in the kernel, the placement check at that layout and (with
# --instantiate) the compiler theorem at it.
#
# Usage: Scc/Test/certify.sh [--arch x64|arm] [--instantiate] [--elf EXE] PROG.w
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
#   4. T.post.lean: the certificate without its decisions at the static link
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
#      no stack need table; or not `Scc.Lower.Accepted0`), or a component AN
#      of `placeOKAt` fails at the executable's layout;
#   4  not yet supported: the reader refuses the linker's placement of
#      `.rodata` below the code (`Scc.Cert.Elf.refuseBelowCode`; ld.lld's
#      default, so every arm executable for now);
#   1  failed: scc, the assembler, the linker or the reader fails (a damaged
#      executable), or T.post.lean does not check for another reason;
#   2  usage.
set -u

ARCH=x64; INST=0; ELF=""; SRC=""
while [ $# -gt 0 ]; do
  case "$1" in
    --arch) ARCH="${2:-}"; shift 2 ;;
    --instantiate) INST=1; shift ;;
    --elf) ELF="${2:-}"; shift 2 ;;
    -*) echo "usage: $0 [--arch x64|arm] [--instantiate] [--elf EXE] PROG.w" >&2; exit 2 ;;
    *) [ -z "$SRC" ] || { echo "$0: more than one program" >&2; exit 2; }; SRC="$1"; shift ;;
  esac
done
case "$ARCH" in
  x64) NS=Scc.Cert.PlaceOK.X64 ;;
  arm) NS=Scc.Cert.PlaceOK.A64 ;;
  *) echo "unknown arch $ARCH" >&2; exit 2 ;;
esac
[ -n "$SRC" ] && [ -f "$SRC" ] || { echo "usage: $0 [--arch x64|arm] [--instantiate] [--elf EXE] PROG.w" >&2; exit 2; }
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

if [ "$ARCH" = x64 ]; then CERT_MODS="Scc.Cert.X64 Scc.Cert.OutStageX64 Scc.Cert.E2EX64"
else CERT_MODS="Scc.Cert.Arm Scc.Cert.OutStageA64 Scc.Cert.E2EA64"; fi
(cd "$ROOT" && $LAKE build scc scc_x64 scc_arm Scc.Cert.Elf Scc.Cert.SrcTerm $CERT_MODS) >/dev/null 2>&1 \
  || verdict 1 "failed: lake build scc"
if [ $INST = 1 ]; then
  if [ "$ARCH" = x64 ]; then THM_MOD=Spike.Lib.LowerX64.Correct; else THM_MOD=Spike.Lib.LowerA64.Correct; fi
  (cd "$ROOT" && $LAKE build "$THM_MOD") >/dev/null 2>&1 || verdict 1 "failed: lake build $THM_MOD"
fi
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK" || exit 1
cp "$SRCABS" "$T.w"

# 1. Compile, with the certificate.
"$SCC" --arch "$ARCH" --cert "$T.cert.lean" -o "$T.s" "$T.w" >"$T.scc.out" 2>"$T.scc.err" \
  || verdict 1 "failed: scc: $(head -c 2000 "$T.scc.err")"
OUTSIDE="-- outside the certified fragment: no stack need table (non-tail recursion)"
if grep -qxF -- "$OUTSIDE" "$T.cert.lean"; then
  verdict 3 "not certifiable: outside the certified fragment (no stack need table: non-tail recursion)"
fi
hs=$(sha256sum "$T.w" | cut -d' ' -f1); ha=$(sha256sum "$T.s" | cut -d' ' -f1)
if [ "$(grep -c "^-- SHA-256 (UTF-8): \($hs\|$ha\)\$" "$T.cert.lean")" != 2 ]; then
  verdict 1 "failed: the certificate's digests differ from sha256sum"
fi
if grep -q '^theorem prog_not_accepted' "$T.cert.lean"; then
  verdict 3 "not certifiable: outside the certified fragment (not Scc.Lower.Accepted0)"
fi

# 2. Assemble and link (run.sh's commands), or take the given executable.
if [ -n "$ELF" ]; then
  cp "$ELF" "$T"
elif [ "$ARCH" = x64 ]; then
  { as -o "$T.o" "$T.s" && ld -static -o "$T" "$T.o"; } 2>"$T.link.err" \
    || verdict 1 "failed: assemble/link: $(head -c 2000 "$T.link.err")"
else
  clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o "$T" "$T.s" 2>"$T.link.err" \
    || verdict 1 "failed: assemble/link: $(head -c 2000 "$T.link.err")"
fi
he=$(sha256sum "$T" | cut -d' ' -f1)

# 3. The reader, by evaluation.
cat >"$T.elf.lean" <<EOF
import Scc.Cert.Elf
#eval show IO Unit from do
  match Scc.Cert.Elf.elfParts (← IO.FS.readBinFile "$REL/$T") with
  | .error e => IO.println s!"certify-elf: refused: {e}"
  | .ok _ => IO.println "certify-elf: ok"
EOF
r=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.elf.lean" 2>&1 | sed -n 's/^certify-elf: //p' | head -n 1)
case "$r" in
  ok) ;;
  "refused: data symbol "*" below the code")
    verdict 4 "not yet supported: rodata below code (the reader ${r#refused: }; the linker's placement)" ;;
  "refused: unexpected mapped section .note.gnu.build-id")
    verdict 4 "not yet supported: build-id note (the reader ${r#refused: }; the linker's default)" ;;
  refused:*) verdict 1 "failed: the ELF reader refuses $T: ${r#refused: }" ;;
  *) verdict 1 "failed: the ELF reader could not be run" ;;
esac

# 4. The certificate after the link.
if [ "$ARCH" = x64 ]; then
  HPA="Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs"; TEXT="⟨asm, sizes, labelOffs⟩"
  CORRECTE="Scc.Sem.X64.CorrectE"; THM="Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt"
  CODEEND="Scc.Sem.X64.codeEnd"; E2E="Scc.Cert.E2E.X64"; E2E_MOD="Scc.Cert.E2EX64"
else
  CODEEND="Scc.Sem.A64.codeEnd"; E2E="Scc.Cert.E2E.A64"; E2E_MOD="Scc.Cert.E2EA64"
  HPA="Scc.Cert.Link.A64.parsesTo asm out.prog out.secs"; TEXT="asm"
  CORRECTE="Scc.Sem.A64.CorrectE"; THM="Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt"
fi
L="⟨elf.1⟩"
{
  echo "import Scc.Cert.Elf"
  echo "import $E2E_MOD"
  if [ $INST = 1 ]; then echo "import $THM_MOD"; fi
  # The certificate up to its decisions at the static link (they are not
  # needed: the decisions below are at the executable's layout).
  sed -e '/^\/-- A1, A2, A4 and A7 of `outLit`/,$d' "$T.cert.lean"
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

/-- The code the canonical loader lays out from \`outLit\` ends where the
executable's code region does (kernel-checked). -/
theorem prog_codeEnd : $CODEEND elf.1.code.lo outLit.prog = elf.1.code.lo + elf.1.code.size :=
  $E2E.codeEnd_eq_of_codeFills (o := outLit) (Λ := elf.1) (by decide +kernel)

/-- A1, A2, A4 and A7 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_1 : ($NS.a1 outLit $L && $NS.a2 outLit $L &&
    $NS.a4 placeCfg outLit $L && $NS.a7 outLit $L) = true := by
  decide +kernel

/-- A3 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_3 : $NS.a3 outLit $L = true := by
  decide +kernel

/-- A5 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_5 : $NS.a5 outLit $L = true := by
  decide +kernel

/-- A6 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_6 : $NS.a6 outLit $L = true := by
  decide +kernel

/-- A8 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_8 : $NS.a8 outLit $L = true := by
  decide +kernel

/-- A9 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_9 : $NS.a9 outLit $L = true := by
  decide +kernel

/-- A11 of \`outLit\` at the executable's layout (kernel-checked). -/
theorem prog_placeOKAt_11 : $NS.a11 outLit $L = true := by
  decide +kernel

/-- **\`placeOKAt\` of \`scc\`'s output at the executable's layout**, from its
components (\`placeOKAt_of\`). -/
theorem prog_placeOKAt : $NS.placeOKAt placeCfg elf.1 out = true := by
  have h1 := prog_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact $NS.placeOKAt_of
    h1.1.1.1 h1.1.1.2 prog_placeOKAt_3 h1.1.2 prog_placeOKAt_5 prog_placeOKAt_6 h1.2 prog_placeOKAt_8
    prog_placeOKAt_9 prog_placeOKAt_11

/-- **Acceptance and placement at the executable's layout.** -/
theorem prog_linked_ready : Scc.Lower.Accepted0 prog_src = true ∧ $NS.placeOKAt placeCfg elf.1 out = true :=
  ⟨prog_accepted, prog_placeOKAt⟩
EOF
  if [ $INST = 1 ]; then cat <<EOF

/-- \`prog_src\`'s one declaration. -/
abbrev main : CoreTerm.Decl := prog_src.head (by decide)

/-- **The compiler theorem at the executable's layout**: \`asm\` is correct
at every admissible entry state, at the layout read from the executable
(with \`main\`'s immediates), for every budget and memory model, given the
loader's parse of \`asm\` (\`hpa\`, the \`#guard\` above: the trust boundary). -/
theorem prog_correct_linked (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : $HPA = true) :
    $CORRECTE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) prog_src)
      { elf.1 with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf main } B $TEXT :=
  $THM (cfg := config) (pcfg := placeCfg) elf.1 prog_accepted prog_placeOKAt hpa

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

rm -f post.rss
if (cd "$ROOT" && "$ROOT/Scc/Test/rssanon.sh" "$WORK/post.rss" "$LAKE" env lean "$WORK/$T.post.lean") \
    >"$T.post.out" 2>&1; then
  secs=""; ra=""; [ -f post.rss ] && IFS=: read -r secs ra <post.rss
  m=""; [ -n "$ra" ] && m=", $((ra / 1024)) MB RssAnon peak"; [ -n "$secs" ] && m=" (${secs} s$m)"
  if [ $INST = 1 ]; then verdict 0 "certified$m: $T.post.lean"
  else verdict 10 "placement decided$m (not certified: the theorem is not instantiated; --instantiate): $T.post.lean"; fi
fi

# 5. It does not check: is it `placeOKAt` that fails, and at which component?
{
  echo "import Scc.Cert.Elf"
  sed -e '/^\/-- `out` as a literal/,$d' "$T.cert.lean" | awk '
    function flush() { if (nd) printf "%s", doc; doc = ""; nd = 0 }
    skip && /^[ \t]/ { next }
    { skip = 0 }
    /^theorem / { doc = ""; nd = 0; skip = 1; next }
    indoc { doc = doc $0 "\n"; if ($0 ~ /-\/[ \t]*$/) indoc = 0; next }
    /^\/--/ { flush(); doc = $0 "\n"; nd = 1; if ($0 !~ /-\/[ \t]*$/) indoc = 1; next }
    { flush(); print }
    END { flush() }'
  cat <<EOF
def elf : Scc.Sem.Layout × String := scc_elf_layout% "$REL/$T"
#eval IO.println (match Scc.Cert.PlaceOK.Checks.firstFail ($NS.checks placeCfg) (fun _ => $L) out with
  | some n => s!"certify-diag: a{n}"
  | none => "certify-diag: none")

end SccCertificate
EOF
} >"$T.diag.lean"
an=$(cd "$ROOT" && "$LAKE" env lean "$WORK/$T.diag.lean" 2>&1 | sed -n 's/^certify-diag: //p' | head -n 1)
case "$an" in
  a[0-9]*) verdict 3 "not certifiable: placeOKAt fails at the executable's layout (component ${an^^}; diagnostic by evaluation)" ;;
  *) verdict 1 "failed: $T.post.lean does not check (placeOKAt: ${an:-?}): $(grep -m1 -A3 'error' "$T.post.out" | head -c 2000)" ;;
esac
