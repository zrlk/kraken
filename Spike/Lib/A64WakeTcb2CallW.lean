/-
**wc_main's second `scc_rt_alloc_tcb` call block inside the global
owned-words map** (AArch64): the block `tcb2Call` at `.sp3`
(`Spike/Lib/A64WakeTcb2Call.lean`) inside `SFactsSt2` at `ownG`
(`tcb2Call_ownG`), proved at the first instance's constant owned words
`ownW L a 16` (`blk_switch2`) and moved to `ownG`, which picks them at the
block's pcs (the final `ownW (phW pc)` branch, `phW = 16`) and at the
callee's entry on a pool stack (`own2a (ph2a 2164712)`, `own1_own2a_ph`);
and the outside move retargeted to any range (`tcbWG_takeK`), so one
`K := PhRec.K L rS'` serves the whole segment.

- `takeK_none`, `blkW_takeK`, `nodeW_takeK`, `tcbWG_takeK`: no take move
  at one range is none at any other.
- `blkPh_const_of`: `blkPh` at a constant phase map from the block's pcs'
  `okPc`.
- `blk_switch2`: any covered `ret`-free block, after the take, at the
  constant instance `o`, inside `SFactsSt2` at a map agreeing with `o`.
- `BandSp3`: **main's frame at `.sp3` on a pool stack** (the hypothesis
  `WcMid` supplies from main's frame facts): `BandA` of the callee's region
  `R.callee (-80) (-192) 0`.
- `sp3_facts`, `own_sp3`, `own_fn`: `ownG` is `ownW L a 16` at the block's
  pcs and at the callee's entry.
- `tcb2Call_ownG`: the result; `tcb2W_ownGK`: the callee's at the same `K`.
-/
import Spike.Lib.A64WakeTcb2W

namespace Spike.Lib.A64.WakePh.Tcb2CallW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.Ret0 (TakeK StackM)
open Spike.Lib.A64.WakePh.Tcb2Call (tcb2Call tcb2Call_ok tcb2Call_pc wake_tcb2CallIn tcb2CallIn wcN3)
open Spike.Lib.A64.WakePh.Tcb2W (BandA PcA good2a_of blkW_toSt2 tcb_labs)

/-! ### The outside move at any range -/

section TakeK

variable {W : Frag isaLSE2} {a : Int64} {rS rS' : Range} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **No take move at `rS` is none at `rS'`**: a take moves any state at
its pc. -/
theorem takeK_none {s : State} (h : ∀ s', ¬ TakeK a rS s s') : ∀ s', ¬ TakeK a rS' s s' :=
  fun _ hk => let ⟨pm, _⟩ := hk.2; h _ ⟨hk.1, pm, rfl⟩

/-- A block's obligations at the take of any range. -/
theorem blkW_takeK {n : ND} {blk : List Directive} (h : BlkW W (TakeK a rS) exe endPc R F n blk) :
    BlkW W (TakeK a rS') exe endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1, takeK_none r.2⟩

/-- A node's obligations at the take of any range. -/
theorem nodeW_takeK {n : ND} (h : NodeW W (TakeK a rS) exe endPc R F n) : NodeW W (TakeK a rS') exe endPc R F n :=
  fun s c hA => ⟨(h s c hA).1, takeK_none (h s c hA).2⟩

/-- **`scc_rt_alloc_tcb`'s node obligations at the take of any range**
(`tcb2W_ownG`'s at `PhRec.K L rS'`). -/
theorem tcbWG_takeK {q : Spike.Lib.A64.Rt.TcbGG}
    (h : ∀ i, Spike.Lib.A64.Rt.TcbWG W (TakeK a rS) exe endPc R F q i) :
    ∀ i, Spike.Lib.A64.Rt.TcbWG W (TakeK a rS') exe endPc R F q i := by
  intro i
  have h := h i
  cases i <;> dsimp only [Spike.Lib.A64.Rt.TcbWG] at h ⊢ <;> first | exact blkW_takeK h | exact nodeW_takeK h

end TakeK

/-! ### A covered block at a constant instance, moved to an agreeing map -/

/-- **`blkPh` at a constant phase map**: every directive classified, every
pc of the block off the sites. -/
theorem blkPh_const_of {okPc : Nat → Bool} {lab : Label → Int64} {pc ra : Int64} {blk : List Directive}
    (hc : blk.all (fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hok : ∀ k < blk.length, okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat = true) :
    Spike.Lib.A64Consumer.blkPh okPc (fun _ => 0) (fun _ => false) lab pc ra blk = true := by
  unfold Spike.Lib.A64Consumer.blkPh
  refine List.all_eq_true.mpr fun k hk => ?_
  have hk' := List.mem_range.mp hk
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hc _ (List.getElem_mem hk'))
  rw [List.getElem?_eq_getElem hk']
  simp only [hok k hk', hd, beq_self_eq_true, Bool.true_and]
  simp

/-- **A covered `ret`-free block across instances**: as `call_switch2` for
any block, its pcs off the sites (`hpc`), after the take, proved at the
constant instance `o` and moved to `own'`, which agrees with `o` at the
block's states and their successors (`hag`). -/
theorem blk_switch2 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own own' : Spike.Lib.A64Consumer.Own}
    {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (o : List (Loc × Val)) {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {l : Label}
    {k : Nat} {lo hi : Int} (hb : Scc.Cert.Rt.A64.blockAt prog l k blk = true)
    (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hcl : blk.all (fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hpc : ∀ k < blk.length, okPc (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hag : BlkW (fun s _ => own' s = o ∧ ∀ s', StSucc μ s s' → own' s' = o) (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n blk) :
    BlkW (fun s _ => SFactsSt2 Λ μ own' s) K exe endPc R (fun m => F m ∧ StackM rS m) n blk := by
  have h := Spike.Lib.A64.Rt.blkW_post (Λ := Λ) (rS := rS) (lbl := lbl) (F := F)
    (Spike.Lib.A64.Rt.InstOk.const hI o True) hb he hok hR hal hlo hhi hC (ra := 0)
    (dead := fun _ => false) (by rw [he]; exact blkPh_const_of hcl hpc)
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM
  exact Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (blkW_toSt2 h) hag

/-! ### `ownG` at the block's pcs and at the callee's entry -/

/-- **Main's frame at `.sp3` on a pool stack**: `scc_rt_alloc_tcb`'s frame
`[-192, 0]` below `sp = R.addr (-80)` (`wc_main`'s region `R`, its 80-byte
frame) in the pool's band. `WcMid` supplies it from main's frame facts. -/
abbrev BandSp3 (L : RuntimeLayout) (R : Region) : Prop := BandA L (R.callee (-80) (-192) 0)

/-- The block's pcs at the canonical base: their values, the phase `16`,
off the sites. -/
theorem sp3_facts : ∀ k < 5, (Int64.ofNat 2169248 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169248 + 4 * k ∧
    phC (2169248 + 4 * k) = 16 ∧ okC (2169248 + 4 * k) = true := by decide +kernel

variable {L : RuntimeLayout}

/-- `.sp3` at the canonical base. -/
theorem lab_sp3 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label ".L21_wc_main.sp3" = Int64.ofNat 2169248 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- **`ownG` at the block's pcs** is `ownW L a 16` (no range of `ownG`'s
holds, `phW = 16`). -/
theorem own_sp3 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {s : State} {k : Nat} (hk : k < 5)
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label ".L21_wc_main.sp3" + Int64.ofNat (4 * k)) :
    ownG L a s = ownW L a 16 := by
  have hp : pcOf s = 2169248 + 4 * k := by
    unfold pcOf; rw [hs, lab_sp3 hlab]; exact (sp3_facts k hk).1
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, e9⟩ := labs_eq hlab (L := L)
  rw [ownG_W hlab (.inr (.inr ⟨?_, ?_, ?_, ?_⟩)), hp, phW_eq, (sp3_facts k hk).2.1] <;> unfold inPc <;> omega

/-- **`ownG` at the callee's entry**, `sp` at `R.addr (-80)` on a pool
stack: `own2a (ph2a 2164712)`, the first instance's `ownW L a 16`. -/
theorem own_fn (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {R : Region} (hb : BandSp3 L R) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.AllocTcb.fnL)
    (hsp : s.st.1.regs.SP.toBitVec = R.addr (-80)) : ownG L a s = ownW L a 16 := by
  obtain ⟨eFn, -, -, -, -, -⟩ := tcb_labs hlab (L := L)
  have hp : pcOf s = 2164712 := by unfold pcOf; rw [hs, eFn]; rfl
  have hg := good2a_of hlab hb (s := s) (by rw [hs, eFn]; decide)
    ⟨0, by decide, Int.le_refl _, by rw [hsp, Region.callee_addr]; rfl⟩
  rw [ownG_2a hlab hg, hp, ← own1_own2a_ph, phW_eq, allocTcb2_ph.1]

/-! ### The block -/

/-- **The second call's block at `.sp3` inside `SFactsSt2` at `ownG`**,
after the take (`hsub`, `hSM` at main's range `rS`), at the outside move of
any range `rS'`: `blk_switch2` at the first instance (`instOkW`, constant
`ownW L a 16`), `ownG` agreeing there at the block's pcs (`own_sp3`) and at
the callee's entry (`own_fn`, main's frame on a pool stack `hb`). -/
theorem tcb2Call_ownG (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) {J : Spike.Lib.A64.Flow.AS → Prop}
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo3 : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hb : BandSp3 L R) {F : MachineData → Prop} {rS : Range} (rS' : Range)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS')
      L.exe L.endPc R (fun m => F m ∧ StackM rS m) (wcN3 L.lab J c0) tcb2Call := by
  obtain ⟨-, -, -, -, -, eSite⟩ := tcb_labs hlab (L := L)
  have e3 := lab_sp3 hlab (L := L)
  have hin := hp ▸ wake_tcb2CallIn
  simp only [tcb2CallIn, Bool.and_eq_true] at hin
  have hlen : tcb2Call.length = 5 := by decide
  have hsp : ∀ {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS},
      Spike.Lib.A64.Flow.Abs R o m σ → m.regs.SP.toBitVec = R.addr o.sp :=
    fun hA => by rw [hA.regs]; exact hA.so .SP _ rfl
  refine blk_switch2 (instOkW hp hlo a (fun _ => True) hsite (rS := rS')) (ownW L a 16) hin.1
    (Spike.Lib.A64.Flow.ofNat4_zero _) tcb2Call_ok hR hal hlo3 hhi (fun _ _ hJ => hJ.1 ▸ hC0) (by decide)
    (by decide) (fun k hk => ?_) hsub hSM ?_
  · show Scc.Cert.Rt.A64.okPcOf lo wakeProg L.Λ
      ((_root_.Executable.labels L.exe).label ".L21_wc_main.sp3" + Int64.ofNat (4 * k)).toBitVec.toNat = true
    rw [okPc_eq hΛ, e3, (sp3_facts k (hlen ▸ hk)).1]; exact (sp3_facts k (hlen ▸ hk)).2.2
  refine Spike.Lib.A64ConsumerA.BlkW.leaf (Spike.Lib.A64.Flow.code_of L.lays rfl hin.1
    (Spike.Lib.A64.Flow.ofNat4_zero _)) tcb2Call_ok hR hal hlo3 hhi ?_ ?_ ?_
  · intro x hx k hk
    rw [hsite, show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 from eSite] at hx
    cases hx
    show ((_root_.Executable.labels L.exe).label ".L21_wc_main.sp3" + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [e3, (sp3_facts k (hlen ▸ hk)).1]
    have : (Int64.ofNat 2165940).toBitVec.toNat = 2165940 := rfl
    omega
  · intro σ c hJ k hk s m hA he hn hs
    exact own_sp3 hlab (hlen ▸ hk) (by rw [hs]; rfl)
  · intro σ c hJ k hk s m hA he hn hs
    rcases Nat.lt_or_ge (k + 1) 5 with hk1 | hk1
    · rw [Spike.Lib.A64.Flow.arun_pc _ tcb2Call_ok (by rw [hlen]; exact hk1)] at hs
      exact own_sp3 hlab hk1 (by rw [hs]; rfl)
    · have ht : tcb2Call.take (k + 1) = tcb2Call := List.take_of_length_le (by omega)
      rw [ht] at hA hs
      obtain ⟨h1, h2⟩ := tcb2Call_pc (_root_.Executable.labels L.exe).label
        ((_root_.Executable.labels L.exe).label ".L21_wc_main.sp3") σ
      refine own_fn hlab hb (by rw [hs]; exact h1) ?_
      have e := hsp hA
      rw [show (wcN3 L.lab J c0).pc = (_root_.Executable.labels L.exe).label ".L21_wc_main.sp3" from rfl,
        show (wcN3 L.lab J c0).o = Tcb2Call.oW from rfl, h2] at e
      rw [hs]; exact e

/-- **`tcb2W_ownG` at the outside move of any range `rS'`** (`tcbWG_takeK`):
the callee's node obligations at `PhRec.K L rS'`, its frame condition still
main's range `rS`. -/
theorem tcb2W_ownGK (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64) {rS : Range} (rS' : Range)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hb : BandA L R) (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (hra : g.ra = (L.lab ".L21_wc_main.sp4").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true
      ⟨Spike.Lib.A64.Rt.hdrA L.lab (Tcb2Call.tcb2Q g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Rt.hdrA L.lab (Tcb2Call.tcb2Q g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.A64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s)
      (Spike.Lib.A64.PhRec.K L rS') L.exe L.endPc R (fun m => F m ∧ StackM rS m) (Tcb2Call.tcb2Q g c0) i :=
  tcbWG_takeK (Tcb2W.tcb2W_ownG hp hlo a hsite hΛ hlab hsep hhdr hC0 hR hal hlo' hhi hb g hra hmP hmH hunP hunH
    hsub hSM)

/-- info: 'Spike.Lib.A64.WakePh.Tcb2CallW.tcb2Call_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcb2Call_ownG

/-- info: 'Spike.Lib.A64.WakePh.Tcb2CallW.tcbWG_takeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcbWG_takeK

end Spike.Lib.A64.WakePh.Tcb2CallW
