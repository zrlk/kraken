/-
**main's source placed in `scc_rt_alloc`** (AArch64; `allocW_WS`
premise `hpl`): at every node of the box's allocator, called from `wc_main`
(`WcPreW.alloc`: region `wAR R`, the call context `WcCtx`), main's source is
placed (`PlacedSE`) as at the call: the allocator's nodes keep the source's
term and environment (`q.c0`, its `holdCtr`), and main's `ThreadId` word in
its frame slot `-80` sits below the callee's region, kept (`CKept`,
`DFrame`), there `wcJ`'s saved `x0`.

- `placedSE_congr`: `PlacedSE` reads only the term and the environment.
- `allocN_ctl`: every allocator node's control is `q.c0`'s up to the hold.
- `placeVal_slot_keptW`: a main slot at `-80` or above across the
  allocator's call (frame 160).
- `allocW_placed`: the instance, from the source at the call placed given
  main's id at main's slot (`hP`) and `Jc`'s `x0` main's id (`hJc`).
- `placedSE_newAt`: `hP` at the box's `new` (`let o = new z in boxTerm`):
  `z` the immediate `0`, `me` main's id at any place; `allocW_placed_new`
  the two composed; `newTerm_eq`, `hiz_immsW`: `hiz` at wake's table.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeHMid
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.WakeImmsW
import Spike.Lib.A64WakeCode

namespace Spike.Lib.A64.WakePh.PlacedAlloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (wAR WcCtx wcJ wN boxTerm)
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE PlacedS envsOf termsOf fvOf)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeSrcCtl (placedSE_of_tbl rep_at)

/-- **`PlacedSE` reads only the term and the environment.** -/
theorem placedSE_congr {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c c' : Ctl} {fs : List TermRun.Frame}
    (ht : c.term = c'.term) (he : c.env = c'.env) (h : PlacedSE Λ lbl s c' fs) : PlacedSE Λ lbl s c fs := by
  unfold PlacedSE PlacedS envsOf termsOf fvOf at *
  rw [ht, he]; exact h

/-- **Every allocator node's control is the call's** up to the hold. -/
theorem allocN_ctl {lab : Label → Int64} {ms : MemSide isaLSE2} {q : Call} :
    ∀ (i : Spike.Lib.A64.Alloc.AN) (σ : Flow.AS) (c : Ctl), (N lab ms q i).J σ c → c.term = q.c0.term ∧ c.env = q.c0.env := by
  intro i σ c h
  cases i <;>
    simp only [N, Spike.Lib.A64.Alloc.Jc, Spike.Lib.A64.Alloc.Jok, Spike.Lib.A64.Alloc.Jslow,
      Spike.Lib.A64.Alloc.Jfull] at h <;>
    first
    | (rcases h with ⟨rfl, -⟩ | ⟨o, rfl, -⟩ <;> exact ⟨rfl, rfl⟩; done)
    | (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨⟨rfl, -⟩, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨o, rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨o, ⟨rfl, -⟩, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨o, ⟨rfl, -⟩⟩ := h; exact ⟨rfl, rfl⟩)

/-- **main's slot across the allocator's call**: below the callee's region
(`wAR R`), a cell of main's frame `R` at `-80` or above is as at the call
(`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_keptW {R : Region} {o : Flow.SO} {m1 m' : MachineData} {σC : Flow.AS} {s : State}
    (hA : Flow.Abs R o m1 σC) (hK : CKept R (-80) (-160) 0 m1 m') (hD : Flow.DFrame (wAR R) m' s.st.1) (hR : R.OK)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -80 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-80) (-160) 0).Off (k - -80) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h80 := Region.addr_toNat_of hR (k := -80) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [wAR, Region.callee]; omega))
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hK k hk hc, hj, hv]

section Inst

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isaLSE2} {Jc : Flow.AS → Ctl → Prop} {q : Call}

set_option hygiene false in
/-- The allocator's frame condition at the call (`WcPreW.alloc`'s). -/
local notation "FA" => fun m => F m ∧ Ret0.CallerCells R (-80) (-160) 0 m ∧
  WcCtx ms (_root_.Executable.labels exe).label R Jc q m

set_option hygiene false in
/-- The source at the call placed, given main's id at main's slot `-80`
(under `Jc` at the call's source). -/
local notation "HP" => ∀ s : State, (∃ v, placeVal (machine (kernel 1)) s (.slot (R.addr (-80)).toNat) = some v ∧
  lbl (mainTidLbl 2) = some v) → PlacedSE Λ lbl s q.c0 []

/-- At a state of the allocator whose memory is outside its region as at
`m'` (a node's), with `FA m'`: main's source placed. -/
theorem placed_in (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hJc : ∀ σe c, Jc σe c → lbl (mainTidLbl 2) = some σe.regs.X0.toNat) (hP : (∃ σe, Jc σe q.c0) → HP) {m' : MachineData}
    (hF : FA m') {s : State} (hD : Flow.DFrame (wAR R) m' s.st.1) : PlacedSE Λ lbl s q.c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, ⟨⟨σe, hj, -, -, h80⟩, -⟩, ⟨rfl, -⟩, hK⟩ := hF
  refine hP ⟨σe, hj⟩ s ⟨_, placeVal_slot_keptW hA hK hD hR hlo hhi ⟨by decide, by omega, by omega⟩ (Int.le_refl _), ?_⟩
  rw [h80]; exact hJc σe _ hj

/-- **main's source placed at every node of `scc_rt_alloc`** (`allocW_WS` `hpl`). -/
theorem allocW_placed (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hJc : ∀ σe c, Jc σe c → lbl (mainTidLbl 2) = some σe.regs.X0.toNat) (hP : (∃ σe, Jc σe q.c0) → HP) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (wAR R) FA := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (wAR R) FA
      (N (_root_.Executable.labels exe).label ms q i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (placed_in (s := { s with st := (m, _) }) hR hlo hhi hJc hP hF hD),
      fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (wAR R) FA
      (N (_root_.Executable.labels exe).label ms q i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (placed_in hR hlo hhi hJc hP hF (Flow.DFrame.refl _ _)), fun _ h => h⟩
  exact ⟨hB _ _, hB _ _, hB _ _, hN _, hN _, hB _ _, hN _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hN _,
    hN _, hB _ _, hN _, hB _ _, hN _⟩

end Inst

/-- **The source at the box's `new` placed** (`let o = new z in boxTerm`):
`z` the immediate `0` (the layout's at the term), `me` main's id at `pm`. -/
theorem placedSE_newAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl}
    (pm : Place (machine (kernel 1)).I.RegId) (ht : c.term = .let_ "o" (.new (.var "z")) boxTerm)
    {tz : Ty} (hz : TermRun.lookupE c.env "z" = some (tz, [TermRun.cst (.num 0)]))
    (hme : TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hiz : Λ.imms c.term "z" 0 = some 0)
    (h10 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  simp only [TermRun.evalAt] at hme
  refine placedSE_of_tbl [("z", [.imm 0]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [ht, show exprFv (.let_ "o" (.new (.var "z")) boxTerm) = ["z", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hz] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases ez : x = "z"
    · subst ez; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hz] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h10
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn'
    by_cases ez : x = "z"
    · subst ez; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'; exact hiz
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne em] at hpl

/-- **`allocW_placed` at the box's `new`**, main's id and the source's
facts from the caller's entry `Jc` (`wcJ`'s, at the call's source `q.c0`):
`let o = new z in boxTerm`, `z` the zero word (the layout's immediate there),
`me` main's id, at main's slot `-80`. -/
theorem allocW_placed_new {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {Jc : Flow.AS → Ctl → Prop} {q : Call}
    (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hJc : ∀ σe c, Jc σe c → lbl (mainTidLbl 2) = some σe.regs.X0.toNat)
    (hJs : ∀ σe c, Jc σe c → c.term = .let_ "o" (.new (.var "z")) boxTerm ∧
      (∃ tz, TermRun.lookupE c.env "z" = some (tz, [TermRun.cst (.num 0)])) ∧
      TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hiz : Λ.imms (.let_ "o" (.new (.var "z")) boxTerm) "z" 0 = some 0) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (wAR R)
      (fun m => F m ∧ Ret0.CallerCells R (-80) (-160) 0 m ∧ WcCtx ms (_root_.Executable.labels exe).label R Jc q m) :=
  allocW_placed hR hlo hhi hJc fun ⟨σe, hj⟩ _ h10 =>
    have ⟨ht, ⟨_, hz⟩, hme⟩ := hJs σe _ hj
    placedSE_newAt _ ht hz hme (ht ▸ hiz) h10

/-- **The box's `new` is the lowering's immediate term** (`wakeImm_t1`). -/
theorem newTerm_eq : (.let_ "o" (.new (.var "z")) boxTerm : Expr) = SccCode.wakeImm_t1 := by
  unfold boxTerm SccCode.wakeImm_t1 SccCode.wakeImm_t0 Spike.Lib.WakePreA.spawnTerm; rfl

/-- **`hiz` at wake's immediate table** (`immsW Λ0 wakeImms`, any `Λ0`). -/
theorem hiz_immsW (Λ0 : Scc.Sem.Layout) :
    Spike.Lib.WakeImmsW.immsW Λ0 SccCode.wakeImms (.let_ "o" (.new (.var "z")) boxTerm) "z" 0 = some 0 := by
  rw [newTerm_eq]; simp [Spike.Lib.WakeImmsW.immsW, SccCode.wakeImms]

end Spike.Lib.A64.WakePh.PlacedAlloc

/-- info: 'Spike.Lib.A64.WakePh.PlacedAlloc.allocW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedAlloc.allocW_placed

/-- info: 'Spike.Lib.A64.WakePh.PlacedAlloc.placedSE_newAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedAlloc.placedSE_newAt

/-- info: 'Spike.Lib.A64.WakePh.PlacedAlloc.allocW_placed_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedAlloc.allocW_placed_new

/-- info: 'Spike.Lib.A64.WakePh.PlacedAlloc.hiz_immsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.PlacedAlloc.hiz_immsW
