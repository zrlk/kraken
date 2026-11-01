/-
**hello's start segment from the start pair** (AArch64; the twin of
`A64WakeStartH0B`'s `hst0_of`): from the loaded thread with hello's start control `C0S.c0S` and no frames, a
segment inside hello's level before the allocation at the entry's marks (`W0H`) under the take at the take site or
a `clone` refusal at `ClH` (`TakeCKS`), with no exit, from `StartH0G.hello_start_wc_h0G`'s segment (`hG`, inside
`WS` under the take `PhRec.K`, from `_start`'s node to `wc_main`'s heap abort `Q1` or `wc_rodata`'s `Q2`) and the
two exits' segments with no exit (`hC` at `Q1`: `StartH0C.hello_hab_closed`; `hCrd` at `Q2`).

Unlike wake's start (main's box control `c0W` after `wakeTh0`'s tail call, `SegW.prefix_done`), hello's start
control *is* the loaded thread's (`c0S = Ctl.of helloTh0`, `helloTh0.stack = []`), so the start pair is `hG`'s
entry directly (no prefix). Reused from wake as is (layout generic): `LowerA64.entry_atW`/`hpc_ofPlaceW`,
`SegWS.mono_W`/`mono_K`/`seq`/`or_pre`/`mono_pre`, `WakeOHinit.unowned_stack`, `pz_of_unowned`,
`Worker.Wake.AbOffW.marks_target`.

**Open premise `hCrd`** (fix route A): `wc_rodata`'s heap abort exit
(`HelloRd.rX .abort` at the frame `[FR]`, `FR = HelloRdCf.frH c0S.env`) closes as a `SegWS` with no exit. It is
open because the generic allocator's abort exit `Alloc.E .abort` (`A64Alloc`) omits `x30` (the return address
past `.4_full`'s `bl scc_rt_abort`), which `ownGH`/`AcH` need along the heap abort's path (`Alloc.EB .abort`,
used at `wc_main`'s `wXH .abort`, has it); route A strengthens `E .abort`'s post with `x30 = .4_full + 8` and lifts
it through hello's rodata pre-run.

**The frame `frM`** stays generic here (`W0` admits `fs ∈ {[], [frM]}`); the root fixes `frM := frH c0S.env`, which
agrees with `frM := fun c => frH c.env` at the start control `c0S` by definition (`frM_agree`).

- `StartPH`: the start pair (`WakeRoot.StartP`'s twin at `helloTh0`).
- `W0H`: `W0` at the entry's marks, hello's choices (`WakeOPremW.W0W`'s twin; `WS` by `marks_target`).
- `pz_rS0_loadH`: `Pz rS0` at the loaded thread (`StartH0R.pz_rS0_load` at any immediate table).
- `entry_atH`: the start pair is at `_start`'s node with `F = FWN ∧ Pz rS0` (`hG`'s entry).
- `takeCKS_iffH`: the take at the site label is `PhRec.K` at `X0WH`'s states.
- `frM_agree`: the two root choices of `frM` agree at `c0S`.
- `hst0_ofH`: the statement.
-/
import Spike.Lib.A64HelloStartH0C
import Spike.Lib.A64WakeStartH0B
import Spike.Lib.WakeOHinit

namespace Spike.Lib.A64.HelloPh.StartH0B

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram pcOf abi)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeKS TakeCKS CloneErrK)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Flow.Ret0 (entryN)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.DmemPriv (WordsNoneP)
open Spike.Lib (FragS Frag SegWS)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- **The root's two choices of `frM` agree at `c0S`**: `frH c0S.env` (this file's root) and `fun c => frH c.env` at
`c0S`. -/
theorem frM_agree : (fun c : Ctl => Spike.Lib.HelloRdCf.frH c.env) c0S = Spike.Lib.HelloRdCf.frH c0S.env := rfl

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The take site. -/
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-- **The start pair** (`WakeRoot.StartP`'s twin): the loaded thread, hello's start control `c0S` (thread 0 of
`setupStartT 2`), its stack `[]`. -/
def StartPH (E : Entry) : FragS isaLSE2 := fun s c fs =>
  s = Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) ∧ c = c0S ∧ fs = []

/-- **hello's level before the allocation at the entry's marks** (`WakeOPremW.W0W`'s twin): `W0` at `ownGH`,
`arW`, `helloSrc`, the write abort phase, `ClH`, hello's threads abort phase `AcH … pfxM`, `X0WH` at the take
site. -/
abbrev W0H (E : Entry) (Dt : State → Prop) (Ctx : FragS isaLSE2) (lsize : Lsize) (frM : TermRun.Frame) :
    FragS isaLSE2 :=
  Spike.Lib.A64.WakeWf.W0 (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ)
    (Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)) (Spike.Lib.WakeOD.arW hpw i)
    helloSrc Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (Spike.Lib.A64.HelloPh.ClH (Ly))
    (Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) Ctx (L0T (Ly).Λ) lsize frM
    (X0WH (Ly) (AX))

/-- **`Pz rS0` at the loaded thread**: main's stack, in the pool, is off the entry stack's memory
(`WakeOHinit.unowned_stack`; `StartH0R.pz_rS0_load` at any immediate table). -/
theorem pz_rS0_loadH (E : Entry) (hE : E.Ok (Ly).Λ) :
    Spike.Lib.A64Consumer.Pz (RS)
      (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)).st.1 := by
  have hst := (Ly).stacks_sub
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  refine Spike.Lib.A64Consumer.pz_of_unowned (by exact (by decide : (0 : Nat) < 16384))
    (Spike.Lib.WakeOHinit.unowned_stack hpw i hE.1 (Spike.Lib.A64.Rt.rS0_sub (Ly)) ?_ _ rfl)
  show ((Ly).stacksA + 0#64).toNat + 16384 ≤ 2 ^ 64
  rw [BitVec.add_zero]; omega

/-- **The start pair is at `_start`'s node** with the control `c0S`, on the entry stack, the frame condition
`FWN ∧ Pz rS0` (`hello_start_wc_h0G`'s entry; `LowerA64.entry_atW`, `pz_rS0_loadH`). -/
theorem entry_atH (E : Entry) (hE : E.Ok (Ly).Λ) :
    At (Ly).exe (Ly).endPc (entryR E)
      (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ Spike.Lib.A64Consumer.Pz (RS) m)
      (entryN (Ly).lab c0S)
      (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) c0S := by
  obtain ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ := Spike.Lib.LowerA64.entry_atW hpw i c0S hE
  exact ⟨h1, h2, h3, h4, σ, hA, ⟨hF, pz_rS0_loadH hpw i E hE⟩, hJ⟩

/-- **The take at the site label is `PhRec.K` at `X0WH`'s states**: the site's range there is main's stack
(`r0Of = rS0`), and `ClH` holds only at the clone's pc, which `X0WH` excludes. -/
theorem takeCKS_iffH {s s' : State} (hx : X0WH (Ly) (AX) s) :
    TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)) s s' ↔ Spike.Lib.A64.PhRec.K (Ly) (RS) s s' := by
  have hr0 : Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab = RS := by
    show (⟨(Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  obtain ⟨hcl, hsr⟩ := hx
  constructor
  · rintro (⟨hpc, pm, rfl⟩ | ⟨⟨hc, -⟩, -⟩)
    · have hr := (hsr (by unfold pcOf; rw [hpc])).1
      exact ⟨hpc, pm, by rw [hr, hr0]⟩
    · exact (hcl hc).elim
  · rintro ⟨hpc, pm, rfl⟩
    have hr := (hsr (by unfold pcOf; rw [hpc])).1
    exact .inl ⟨hpc, pm, by rw [hr, hr0]⟩

/-- **hello's start segment from the start pair** (`RootOpen.hst0`'s twin): `hG` (`hello_start_wc_h0G`'s segment
at the root's choices, from `_start`'s node at `c0S` with `FWN ∧ Pz rS0`, to `Q1 ∨ Q2`), then the exits' segments
`hC` (at `Q1`, `wc_main`'s heap abort; `hello_hab_closed`) and `hCrd` (at `Q2`, `wc_rodata`'s heap abort; open
row `B8-H0-rdabort`, see the module doc), each with no exit. The start pair is `hG`'s entry (`entry_atH`); the
take at the site label moves `X0WH`'s states as `PhRec.K` (`takeCKS_iffH`); `WS` is `W0H` (`marks_target`). -/
theorem hst0_ofH (E : Entry) (hE : E.Ok (Ly).Λ) (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : TermRun.Frame} {lblS : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} {Q1 Q2 : FragS isaLSE2}
    (hG : SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc Dt
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) lsize frM (X0WH (Ly) (AX)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) helloSrc lblS ms
      ((At (Ly).exe (Ly).endPc (entryR E)
        (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ Spike.Lib.A64Consumer.Pz (RS) m)
        (entryN (Ly).lab c0S)).at [])
      (fun s c fs => Q1 s c fs ∨ Q2 s c fs))
    (hC : SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc Dt
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) lsize frM (X0WH (Ly) (AX)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) helloSrc lblS ms Q1 (fun _ _ _ => False))
    /- open premise: `wc_rodata`'s heap abort exit closes; open because
    `Alloc.E .abort` omits `x30` (module doc) -/
    (hCrd : SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc Dt
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) lsize frM (X0WH (Ly) (AX)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) helloSrc lblS ms Q2 (fun _ _ _ => False)) :
    SegWS (W0H (asm := asm) hpw i E Dt Ctx lsize frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc lblS ms
      (StartPH hpw i E) (fun _ _ _ => False) := by
  have hprog : (Ly).prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  refine (((hG.seq (hC.or_pre hCrd)).mono_K fun s c fs hW s' => takeCKS_iffH hpw i hW.2.1).mono_W
    fun s c fs h => ?_).mono_pre fun s c fs ⟨hs, hc, hfs⟩ => ?_
  · show Spike.Lib.A64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  · subst hs hc hfs
    exact ⟨entry_atH hpw i E hE, rfl⟩

end Place

end Spike.Lib.A64.HelloPh.StartH0B

/-- info: 'Spike.Lib.A64.HelloPh.StartH0B.frM_agree' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0B.frM_agree

/-- info: 'Spike.Lib.A64.HelloPh.StartH0B.pz_rS0_loadH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0B.pz_rS0_loadH

/-- info: 'Spike.Lib.A64.HelloPh.StartH0B.entry_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0B.entry_atH

/-- info: 'Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH

/-- info: 'Spike.Lib.A64.HelloPh.StartH0B.hst0_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0B.hst0_ofH
