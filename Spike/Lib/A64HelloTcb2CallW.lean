/-
**hello.w's `wc_main` second `scc_rt_alloc_tcb` call block inside the
global owned-words map** (AArch64): the twin of
`Spike/Lib/A64WakeTcb2CallW.lean` at helloProg. The block `HelloWc.tcb2CallH`
at `.sp3` (`Spike/Lib/A64HelloWcSp3.lean`, `wc_main`'s 144-byte frame)
inside `SFactsSt2` at `ownGH` (`tcb2Call_ownGH`), proved at the first
instance's constant owned words `ownH L a 16` (wake's generic `blk_switch2`)
and moved to `ownGH`, which picks them at the block's pcs (`phH = 16`) and at
the callee's entry on a pool stack (`own2aH (ph2aH 2164748)`,
`own1_own2aH_ph`); and the callee's node obligations at the outside move of
any range (`tcb2W_ownGKH`, wake's `tcbWG_takeK`).

- `BandSp3H`: main's frame at `.sp3` on a pool stack, `BandAH` of the
  callee's region `R.callee (-144) (-192) 0`.
- `sp3_factsH`, `lab_sp3H`, `own_sp3H`, `own_fnH`: `ownGH` is `ownH L a 16`
  at the block's pcs (`.sp3` at `2169696`) and at the callee's entry.
- `tcb2Call_ownGH`, `tcb2W_ownGKH`: the results.
-/
import Spike.Lib.A64HelloTcb2W
import Spike.Lib.A64WakeTcb2CallW

namespace Spike.Lib.A64.HelloPh.Tcb2CallW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.Ret0 (TakeK StackM)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.HelloPh.WcSp6 (oWH)
open Spike.Lib.A64.Flow.HelloWc (tcb2QH tcb2CallH tcb2CallH_ok tcb2CallH_pc hello_wcSp3InH wcSp3InH wcN3H)
open Spike.Lib.A64.HelloPh.Tcb2W (BandAH PcAH good2aH_of tcb_labsH)
open Spike.Lib.A64.WakePh.Tcb2CallW (blk_switch2 tcbWG_takeK)
open Spike.Lib.A64.WakePh (inPc)

/-! ### `ownGH` at the block's pcs and at the callee's entry -/

/-- **Main's frame at `.sp3` on a pool stack**: `scc_rt_alloc_tcb`'s frame
`[-192, 0]` below `sp = R.addr (-144)` (`wc_main`'s region `R`, its
144-byte frame) in the pool's band. `WcMid` supplies it from main's frame facts. -/
abbrev BandSp3H (L : RuntimeLayout) (R : Region) : Prop := BandAH L (R.callee (-144) (-192) 0)

/-- The block's pcs at the canonical base: their values, the phase `16`,
off the sites. -/
theorem sp3_factsH : ∀ k < 5, (Int64.ofNat 2169696 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169696 + 4 * k ∧
    phC (2169696 + 4 * k) = 16 ∧ okC (2169696 + 4 * k) = true := by decide +kernel

variable {L : RuntimeLayout}

/-- `.sp3` at the canonical base. -/
theorem lab_sp3H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" = Int64.ofNat 2169696 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- **`ownGH` at the block's pcs** is `ownH L a 16` (no range of `ownGH`'s
holds, `phH = 16`). -/
theorem own_sp3H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {s : State} {k : Nat} (hk : k < 5)
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" + Int64.ofNat (4 * k)) :
    ownGH L a s = ownH L a 16 := by
  have hp : pcOf s = 2169696 + 4 * k := by
    unfold pcOf; rw [hs, lab_sp3H hlab]; exact (sp3_factsH k hk).1
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, e9⟩ := labs_eqH hlab (L := L)
  rw [ownGH_W hlab (.inr (.inr ⟨?_, ?_, ?_, ?_⟩)), hp, phH_eq, (sp3_factsH k hk).2.1] <;> unfold inPc <;> omega

/-- **`ownGH` at the callee's entry**, `sp` at `R.addr (-144)` on a pool
stack: `own2aH (ph2aH 2164748)`, the first instance's `ownH L a 16`. -/
theorem own_fnH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {R : Region} (hb : BandSp3H L R) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.AllocTcb.fnL)
    (hsp : s.st.1.regs.SP.toBitVec = R.addr (-144)) : ownGH L a s = ownH L a 16 := by
  obtain ⟨eFn, -, -, -, -, -⟩ := tcb_labsH hlab (L := L)
  have hp : pcOf s = 2164748 := by unfold pcOf; rw [hs, eFn]; rfl
  have hg := good2aH_of hlab hb (s := s) (by rw [hs, eFn]; decide)
    ⟨0, by decide, Int.le_refl _, by rw [hsp, Region.callee_addr]; rfl⟩
  rw [ownGH_2a hlab hg, hp, ← own1_own2aH_ph, phH_eq, allocTcb2H_ph.1]

/-! ### The block -/

/-- **The second call's block at `.sp3` inside `SFactsSt2` at `ownGH`**,
after the take (`hsub`, `hSM` at main's range `rS`), at the outside move of
any range `rS'`: `blk_switch2` at the first instance (`instOkH`, constant
`ownH L a 16`), `ownGH` agreeing there at the block's pcs (`own_sp3H`) and at
the callee's entry (`own_fnH`, main's frame on a pool stack `hb`). -/
theorem tcb2Call_ownGH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo3 : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hb : BandSp3H L R) {F : MachineData → Prop} {rS : Range} (rS' : Range)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS')
      L.exe L.endPc R (fun m => F m ∧ StackM rS m) (wcN3H L.lab c0 sl me cA fr) tcb2CallH := by
  obtain ⟨-, -, -, -, -, eSite⟩ := tcb_labsH hlab (L := L)
  have e3 := lab_sp3H hlab (L := L)
  have hin := hp ▸ hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  have hlen : tcb2CallH.length = 5 := by decide
  have hsp : ∀ {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS},
      Spike.Lib.A64.Flow.Abs R o m σ → m.regs.SP.toBitVec = R.addr o.sp :=
    fun hA => by rw [hA.regs]; exact hA.so .SP _ rfl
  refine blk_switch2 (instOkH hp hlo a (fun _ => True) hsite (rS := rS')) (ownH L a 16) hin.1.1.1.1.1
    (Spike.Lib.A64.Flow.ofNat4_zero _) tcb2CallH_ok hR hal hlo3 hhi (fun _ _ hJ => hJ.1 ▸ hC0) (by decide)
    (by decide) (fun k hk => ?_) hsub hSM ?_
  · show Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg L.Λ
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" + Int64.ofNat (4 * k)).toBitVec.toNat = true
    rw [okPc_eq hΛ, e3, (sp3_factsH k (hlen ▸ hk)).1]; exact (sp3_factsH k (hlen ▸ hk)).2.2
  refine Spike.Lib.A64ConsumerA.BlkW.leaf (Spike.Lib.A64.Flow.code_of L.lays rfl hin.1.1.1.1.1
    (Spike.Lib.A64.Flow.ofNat4_zero _)) tcb2CallH_ok hR hal hlo3 hhi ?_ ?_ ?_
  · intro x hx k hk
    rw [hsite, show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165976 from eSite] at hx
    cases hx
    show ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [e3, (sp3_factsH k (hlen ▸ hk)).1]
    have : (Int64.ofNat 2165976).toBitVec.toNat = 2165976 := rfl
    omega
  · intro σ c hJ k hk s m hA he hn hs
    exact own_sp3H hlab (hlen ▸ hk) (by rw [hs]; rfl)
  · intro σ c hJ k hk s m hA he hn hs
    rcases Nat.lt_or_ge (k + 1) 5 with hk1 | hk1
    · rw [Spike.Lib.A64.Flow.arun_pc _ tcb2CallH_ok (by rw [hlen]; exact hk1)] at hs
      exact own_sp3H hlab hk1 (by rw [hs]; rfl)
    · have ht : tcb2CallH.take (k + 1) = tcb2CallH := List.take_of_length_le (by omega)
      rw [ht] at hA hs
      obtain ⟨h1, h2⟩ := tcb2CallH_pc (_root_.Executable.labels L.exe).label
        ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp3") σ
      refine own_fnH hlab hb (by rw [hs]; exact h1) ?_
      have e := hsp hA
      rw [show (wcN3H L.lab c0 sl me cA fr).pc = (_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" from rfl,
        show (wcN3H L.lab c0 sl me cA fr).o = oWH from rfl, h2] at e
      rw [hs]; exact e

/-- **`tcb2W_ownGH` at the outside move of any range `rS'`** (`tcbWG_takeK`):
the callee's node obligations at `PhRec.K L rS'`, its frame condition still
main's range `rS`. -/
theorem tcb2W_ownGKH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64) {rS : Range}
    (rS' : Range)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hb : BandAH L R) (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (hra : g.ra = (L.lab ".L22_wc_main.sp4").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true
      ⟨Spike.Lib.A64.Rt.hdrA L.lab (tcb2QH g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.A64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s)
      (Spike.Lib.A64.PhRec.K L rS') L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2QH g c0) i :=
  tcbWG_takeK (Tcb2W.tcb2W_ownGH hp hlo a hsite hΛ hlab hsep hhdr hC0 hR hal hlo' hhi hb g hra hmP hmH hunP hunH
    hsub hSM)

/-- info: 'Spike.Lib.A64.HelloPh.Tcb2CallW.tcb2Call_ownGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcb2Call_ownGH

end Spike.Lib.A64.HelloPh.Tcb2CallW
