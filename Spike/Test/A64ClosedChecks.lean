import Spike.Lib.LowerA64.Correct
import Spike.Lib.SrcRun
import Spike.Test.Cert.A64Ret0Cert

/-!
# Checks of `a64_scc_correctE_text_closed` at `ret0`'s certificate

Sanity and refutation checks of the closed AArch64 theorem
(`Spike/Lib/LowerA64/Correct.lean`) at `ret0`'s generated certificate:

- **The source is not trivial**: `prog_src` under `srcP1 arch` reaches the
  trace `[exit 42]` (`src_reach_exit42`, kernel-checked), so the `sim`
  clause of the conclusion constrains the target's observable trace.
- **The premises are decided**: `prog_accepted` and `prog_placeOK` are
  kernel-checked; `hpa` is the certificate's executed `#guard` (re-run
  here), the documented trust boundary.
- **This theorem's layout is the model link**: the conclusion's `Λ` is the
  link at the placement configuration's bases (code at `0x400000`). The
  bases of a real link differ (`clang`/`lld`: text at `0x210370`; GNU `ld`:
  `_start` at `0x401000`); at bases copied from the `lld` link of this text
  `placeOK` fails (`lld_not_placeOK`), and in every model link
  `scc_rt_pinned_next` is 16 bytes after `scc_rt_heap_use`, where both real
  links put it `0x20010` bytes after (the model takes the heap, pinned and
  pool `.zero`s out of the `.bss` walk). So no configuration's model link
  has the real symbol addresses for this text. The real `ld.lld` link is
  covered by the placement check at the layout read off the executable
  instead (`placeOKAt`): `Spike/Test/Ret0LinkedA64.lean`'s
  `ret0_linked_correct` is the release theorem at that layout.
- **Immediates**: the conclusion's `Λ.imms` is `immsOf d`, read off the
  source; the placement check does not read it.
-/

namespace Spike.Test.A64ReviewClosed

open CoreLang CoreTerm
open Scc.Sem Scc.Cert.PlaceOK
open Spike.Lib
open Spike.Lib.A64.Flow.Ret0.Inst (start_run mainEnv exitEnv mainBody)

/-! ## The source has a nontrivial behaviour -/

/-- `ret0`'s `main`. -/
def mainD : Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := mainBody }

theorem prog_src_eq : SccCertificate.prog_src = [mainD] := rfl

/-- The source start's thread. -/
def th0 : TermRun.TTh := { term := .tail "main" [] (.var "a") [], env := [("a", .unit, [])] }

/-- The configuration where `main` has returned `42`. -/
def sEnd : TermRun.Cfg :=
  { ({ SrcSem.mainStart with cap := 1 } : TermRun.Cfg) with
    ths := #[{ th0 with term := .ret (.var "y"), env := exitEnv (mainEnv mainD) }] }

theorem mainExit_sEnd : SrcSem.mainExit sEnd = [.exit 42] := by decide

/-- **`ret0`'s source reaches the exit `42`** under the theorem's source
parameters, for every memory model. -/
theorem src_reach_exit42 (arch : WeakMem.Arch) :
    (SrcSem.source (srcP1 arch) SccCertificate.prog_src).Reach [.exit 42] sEnd := by
  refine ⟨{ SrcSem.mainStart with cap := 1 }, rfl, ?_⟩
  have h := (start_run (p := SccCertificate.prog_src) (d := mainD) rfl rfl).run_source
    (P := srcP1 arch) (.none (srcP1_hooks arch)) (s := { SrcSem.mainStart with cap := 1 }) (th := th0)
    rfl rfl rfl rfl rfl rfl (fun _ h => by cases h) (fun _ h => by rw [srcP1_hooks] at h; cases h)
  have e : ({ ({ SrcSem.mainStart with cap := 1 } : TermRun.Cfg) with
      ths := ({ SrcSem.mainStart with cap := 1 } : TermRun.Cfg).ths.set! 0
        { th0 with term := .ret (.var "y"), env := exitEnv (mainEnv mainD) } } : TermRun.Cfg) = sEnd := rfl
  rw [e, mainExit_sEnd] at h
  exact h

/-- The exit is `42`, not `1`: the conclusion's `sim` clause pins a target
exit to a source trace, and this one is not `[exit 1]`. -/
example : SrcSem.mainExit sEnd ≠ [.exit 1] := by decide

/-! ## The premises at the certificate -/

-- The parse check, the premise `hpa` (executed, not kernel-checked).
#guard Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs

/-- The closed theorem at the certificate: only `hpa` is left. -/
example (B : Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  Spike.Lib.LowerA64.a64_scc_correctE_text_closed (cfg := SccCertificate.config)
    (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch) SccCertificate.prog_accepted
    SccCertificate.prog_placeOK hpa

/-! ## The layout is the model link -/

/-- The conclusion's link (without immediates). -/
abbrev Λc : Scc.Sem.Layout := (A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ

/-- The model puts the text at `0x400000` (a real `lld` link of this text
puts `_start` at `0x210370`, GNU `ld` at `0x401000`). -/
theorem code_lo : Λc.code.lo = 0x400000 := by decide +kernel

/-- In the model link `scc_rt_pinned_next` is 16 bytes after
`scc_rt_heap_use` (both `lld` and GNU `ld` put it `0x20010` bytes after:
`readelf -s` of the linked text gives `0x42216e0`/`0x42416f0` and
`0x4404290`/`0x44242a0`). -/
theorem pinned_next_after_heap_use :
    Λc.symbols.lookup "scc_rt_heap_use" = some 0x600000 ∧
      Λc.symbols.lookup "scc_rt_pinned_next" = some 0x600010 := by decide +kernel

/-- The bases of `clang --target=aarch64-linux-gnu -nostdlib -static
-fuse-ld=lld`'s link of this text (`readelf -S`, `readelf -s`). -/
def lldBases : Scc.Cert.Link.Bases :=
  { codeLo := 0x210370, codeSize := 0x11298, roLo := 0x2001b8, dataLo := 0x221608, heapLo := 0x2216e0,
    poolLo := 0x4241700, pinnedLo := 0x42216f0 }

/-- **At the real link's bases the placement check fails** (A1). -/
theorem lld_not_placeOK :
    A64.placeOK { SccCertificate.placeCfg with bases := lldBases } SccCertificate.out = false := by
  rw [SccCertificate.out_eq]
  exact A64.placeOK_eq_false_of_a1 (by decide +kernel)

-- At the real link's bases the model still puts `scc_rt_pinned_next` 16
-- bytes after `scc_rt_heap_use` (the `lld` link: `0x20010` after).
#guard let Λ := (A64.tablesOf { SccCertificate.placeCfg with bases := lldBases } SccCertificate.outLit).Λ
  match Λ.symbols.lookup "scc_rt_heap_use", Λ.symbols.lookup "scc_rt_pinned_next" with
  | some a, some b => b = a + 16
  | _, _ => false

-- With GNU `ld`'s text base (`0x401000`) and the canonical data bases the
-- placement check passes (executed): the theorem's text base is free, the
-- data layout is the model's.
#guard A64.placeOK { SccCertificate.placeCfg with
  bases := { Scc.Cert.Link.canonical with codeLo := 0x401000, codeSize := 0xff000 } } SccCertificate.outLit

/-! ## Entry states at the conclusion's layout -/

/-- `Entry.linux` is admissible at the conclusion's layout (any immediates). -/
example (i : Expr → String → Nat → Option Nat) :
    Entry.linux.Ok { (A64.tablesOf SccCertificate.placeCfg SccCertificate.out).Λ with imms := i } :=
  ⟨Scc.Cert.PlaceOK.clear_of_below32 (A64.below32_of_placeOK SccCertificate.prog_placeOK),
    by decide, by decide, by decide⟩

/-- A Linux-like stack pointer (`0x7ffc_0000_0000`, ASLR) is admissible. -/
example : Entry.Ok ⟨⟨0x7ffc00000000 - 65536, 65536⟩⟩ Λc := by decide +kernel

/-- A stack of 8 KiB is not (the theorem says nothing about it). -/
example : ¬ Entry.Ok ⟨⟨0x7ffc00000000 - 8192, 8192⟩⟩ Λc := by decide +kernel

end Spike.Test.A64ReviewClosed
