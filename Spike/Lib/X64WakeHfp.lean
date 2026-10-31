/-
**main's frame pointer at the clone** (x86-64):
`X64WakeMainHRI.hMainR_I`'s `hfp` (`fp = (RW Rm).addr 48` at every
`MainSeg`) from the clone's `ClonePost` parts, given the wc entry's stack
pointer `hσC : σC.rsp = R.base + 8`.

- `fp_of_frG`: the caller's saved frame pointer is `σC.rsp + 40`. `wJ0`'s
  `enter` changes only the slots, and `wNC` puts `%rbp` at `%rsp + 40`.
- `slot_eq_of_abs`: two abstractions of one machine state at one region
  agree on its slots.
- `fp_unique`: a `MainSeg`'s `fp` is the word at slot `0` of
  `⟨Rm.base, -64, 16⟩`, so it is any `JS` node's `fp` at that state.
  `Rm.base` is `%rsp + 64`.
- `hfp_of_parts`: `hfp` from `ClonePost`'s `FrG`, its `JS` node, its base
  and `hσC`.

- `hfp_of_clonePost`: `hfp` from `ClonePost`, whose last conjunct is `hσC`
  (row X64-MainHR-hfp-pin, produced by `X64WakeBox.box_rsp`).
- `hfp_W`: `X64WakeMainHRI.hMainR_I`'s `hfp` at `wakeD` with `inv1W`, from
  `OPrem` (`X64WakeHClW.hpostC_W`).

**Where this differs from AArch64**: AArch64's `MainPieces` takes any `x29`
(`WakeMainFrames.frames_unit`). The x86-64 main's tail reads its frame
through `%rbp`, so `MainWS` pins `fp` at `R.addr 48`.
-/
import Spike.Lib.X64WakeHClW
import Spike.Lib.X64WakeMainHR

namespace Spike.Lib.X64WakeHfp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.WakeWc (FrG)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64WakeMainHR (RW)

/-- **The caller's saved frame pointer** is `σC`'s `%rsp + 40`: `wJ0`'s
`enter` keeps the registers, `wNC`'s `%rbp` is `%rsp + 40`. -/
theorem fp_of_frG {lab : Label → Int64} {J : AS → Ctl → Prop} {σC : AS} {fr : BitVec 64 × BitVec 64}
    (h : FrG (WakeM.wJ0 (WakeM.wNC lab J).J σC) fr) : fr.1 = σC.regs.get64 .rsp + 40#64 := by
  obtain ⟨σe, c, ⟨rfl, -, -, -, h⟩, rfl⟩ := h
  exact h

/-- **Two abstractions of one machine state at one region agree on its
slots.** -/
theorem slot_eq_of_abs {R : Region} {o o' : SO} {m : MachineData} {σ σ' : AS} (h : Abs R o m σ)
    (h' : Abs R o' m σ') {k : Int} (hk : R.Off k) : σ.slot k = σ'.slot k := by
  obtain ⟨j, hj, e⟩ := h.slot k hk
  obtain ⟨j', hj', e'⟩ := h'.slot k hk
  rw [hj] at hj'
  cases hj'
  rw [← e, ← e']

/-- **A `MainSeg`'s `fp` is the frame's word at `0`**: any `JS` node at the
same state over `⟨R.base, -64, 16⟩`, `R.base` the same `%rsp + 64`, has the
same `fp`. -/
theorem fp_unique {L : RuntimeLayout} {endPc endPc' : Int64} {th : Thread isa} {c c' : Ctl} {Rm R : Region}
    {F₂ F' : MachineData → Prop} {cA fp ra tp cA' fp' ra' tp' : BitVec 64} {pc : Int64} {o : SO}
    (hM : X64WakeMainHRD.MainSeg L endPc th c Rm F₂ cA fp ra tp)
    (hat : At L.exe endPc' ⟨R.base, -64, 16⟩ F' ⟨pc, o, JS c' cA' fp' ra' tp'⟩ th.st c')
    (hb : (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64) : fp = fp' := by
  have hRb := hM.hRb
  have e : Rm.base = R.base := BitVec.eq_of_toNat_eq (by omega)
  obtain ⟨-, -, -, -, σ, hA, -, -, -, h0, -⟩ := hM.hhat
  obtain ⟨-, -, -, -, σ', hA', -, -, -, h0', -⟩ := hat
  rw [e] at hA
  rw [← h0, ← h0']
  exact slot_eq_of_abs hA hA' (show (0 : Int) % 8 = 0 ∧ (-64 : Int) ≤ 0 ∧ (0 : Int) + 8 ≤ 16 by decide)

/-- **`hfp` from `ClonePost`'s parts**: its `FrG`, its `JS` node at the
clone state, its base `%rsp + 64` and the wc entry's stack pointer `hσC`. -/
theorem hfp_of_parts {L : RuntimeLayout} {endPc endPc' : Int64} {th : Thread isa} {c c' : Ctl} {Rm R : Region}
    {F₂ F' : MachineData → Prop} {cA fp ra tp cA' : BitVec 64} {t : UInt64} {J : AS → Ctl → Prop} {σC : AS}
    {fr : BitVec 64 × BitVec 64}
    (hM : X64WakeMainHRD.MainSeg L endPc th c Rm F₂ cA fp ra tp)
    (hfr : FrG (WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) fr)
    (hat : At L.exe endPc' ⟨R.base, -64, 16⟩ F' ⟨cloneAt L.exe, oW, JS c' cA' fr.1 fr.2 t.toBitVec⟩ th.st c')
    (hb : (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hσC : σC.regs.get64 .rsp = R.base + 8#64) : fp = (RW Rm).addr 48 := by
  have hRb := hM.hRb
  have e : Rm.base = R.base := BitVec.eq_of_toNat_eq (by omega)
  rw [fp_unique hM hat hb, fp_of_frG hfr, hσC, BitVec.add_assoc]
  simp only [Region.addr, e]
  rfl

/-- **`hfp` from `ClonePost`** (whose last conjunct is the wc entry's stack
pointer): every `MainSeg` at the clone state has `fp = (RW Rm).addr 48`. -/
theorem hfp_of_clonePost {L : RuntimeLayout} {endPc endPc' : Int64} {J : AS → Ctl → Prop} {t : UInt64}
    {th : Thread isa} {c c' : Ctl} (h : WakeWc.ClonePost L endPc' J t th.st c') {Rm : Region}
    {F₂ : MachineData → Prop} {cA fp ra tp : BitVec 64}
    (hM : X64WakeMainHRD.MainSeg L endPc th c Rm F₂ cA fp ra tp) : fp = (RW Rm).addr 48 := by
  obtain ⟨R, _, σC, _, _, fr, hfr, _, _, hat, hb, _, _, hσ⟩ := h
  exact hfp_of_parts hM hfr hat hb hσ

section Inst

open Spike.Lib.X64WakeSpawnR (ιR QG PreR)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeA64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

variable {asm : Scc.Sem.X64.Asm} {E : Scc.Sem.Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop}
  {μ : Marks} {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {B : Scc.Sem.Budget}
  {Ab Ac : State → Prop} (cT : Loc) (Dt : State → Prop) (ls0 : Spike.Lib.X64Consumer.Lsize) (Ctx : FragS isa)
  (frM : TermRun.Frame) (inv0 : FragS isa)

set_option hygiene false in
/-- `wakeD` at the levels `W0W`, `W1W` and `h1`'s invariant `inv1W`. -/
local notation "DH" =>
  X64.WakeOD.wakeD hp i E cT Dt ls0 (X64.WakeOPremW.W0W asm hp i E Dt Ctx ls0 frM) inv0
    (X64.WakeOPremW.W1W asm hp i E Dt Ctx ls0) (X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0)

/-- **`X64WakeMainHRI.hMainR_I`'s `hfp`** at `wakeD` with `inv1W`, from
`OPrem` (`X64WakeHClW.hpostC_W`, `hfp_of_clonePost`). -/
theorem hfp_W
    (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ ((target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ)
      DH d s)
    (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∀ Rm F₂ cA fp ra tp,
        X64WakeMainHRD.MainSeg (Ly) (X64WakeAssemblyR.endR hp i) th (Ctl.of s0) Rm F₂ cA fp ra tp →
        fp = (RW Rm).addr 48 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
    Rm F₂ cA fp ra tp hM
  obtain ⟨J, t, h⟩ := X64WakeHClW.hpostC_W hp i cT Dt ls0 Ctx frM inv0 hR1 hO
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  exact hfp_of_clonePost h hM

end Inst

end Spike.Lib.X64WakeHfp

/-- info: 'Spike.Lib.X64WakeHfp.fp_of_frG' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHfp.fp_of_frG

/-- info: 'Spike.Lib.X64WakeHfp.fp_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHfp.fp_unique

/-- info: 'Spike.Lib.X64WakeHfp.hfp_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHfp.hfp_of_parts

/-- info: 'Spike.Lib.X64WakeHfp.hfp_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHfp.hfp_W
