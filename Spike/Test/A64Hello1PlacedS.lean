/-
**`scc_rt_alloc`'s frames placed at `hello1.w`'s instance** (AArch64): the
allocator's node obligations (`AllocW`, `Spike/Lib/A64Alloc.lean`) inside
`W0`'s placement component (`PlacedS`) under `rodata`'s frame, the setup
frame `setupFrame e env` reading only `me`, in `scc_rt_main`'s cell `-80`
(the thread pointer, `rdJ'`, `mJ`).

- `wpRep_slot`: a word at a mapped 8-byte address represents its number.
- `framesPlaced_setup`: the setup frame placed with `me` at a place.
- `placed_rdN`: a control at `rodata`'s allocation (`rdCN`'s term and
  environment) placed, `m` the immediate `2` of the layout's table.
- `ctl_of_N`, `allocW_of_ctl`: every node of `scc_rt_alloc` is at the call's
  control or its hold; a predicate of such controls at every memory the
  node's frame condition and a frame of its region reach holds at every
  node.
- `allocPlaced`: every node of `scc_rt_alloc` in `wc_rodata`'s call context
  (`RdPreW.alloc`'s frame condition at `MainPreW.rd`'s, `rdJ'`'s source)
  places the frames `[setupFrame e env]`.
-/
import Spike.Test.A64Hello1AllocArena
import Spike.Lib.A64PlacedS
import Spike.Lib.A64Hello1SetupGlue

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide Ctl Frag)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND AS Abs DFrame CKept enter holdCtr)
open Spike.Lib.A64.Flow.Hello1 (setupFrame rdJ' mF mR mNC mRdJ0 mJ aR RdCtx rN rdJ)
open Spike.Lib.A64.Flow.Ret0 (MainG CallerCells)
open Spike.Lib.A64ConsumerS (PlacedS FramesPlaced)
open Spike.Lib.Hello1RodataSrc (rdCN eB envN)
open SccCode (hello1Λ)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## The setup frame -/

/-- **A word at a mapped address represents its number**: the 8 bytes at
`a` load `j`, of bits `t`. -/
theorem wpRep_slot {a : BitVec 64} {j : Int} {t : BitVec 64} (h : Mem.loadInt s.st.1.dmem a 8 = some j)
    (ht : BitVec.ofInt 64 j = t) :
    WordPlaceRep (machine (kernel 1)) lbl s (.one (.slot a.toNat)) (.num t.toNat) := by
  refine ⟨t.toNat, ?_, t.isLt, rfl⟩
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = some t.toNat
  simp [Scc.Sem.A64.privLoad, h, ht]

/-- **The setup frame placed** with `me` at the place `pl` (a register
before `scc_rt_main` saves it, its slot after): the frame's body reads no
variable but `me` (and its binder `r`), `me` is one word `w`, represented
at `pl`. -/
theorem framesPlaced_setup {e : Expr} {env : TermRun.Env} {w : TermRun.Word}
    {pl : Place (machine (kernel 1)).I.RegId}
    (hfv : ∀ y ∈ (exprFv e).filter (· != "r"), y = "me")
    (hme : ∀ ty ws, TermRun.lookupE env "me" = some (ty, ws) → ws = [w])
    (hrep : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    FramesPlaced Λ lbl s [setupFrame e env] := by
  refine ⟨fun d x k => if d = 0 ∧ x = "me" ∧ k = 0 then some (.one pl) else none, ?_, ?_, ?_⟩
  · intro d f hf x ty ws hx k wd wp hwd hwp
    dsimp only at hwp
    split at hwp
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      cases hwp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      rw [hme ty ws hx] at hwd
      cases hwd
      exact hrep
    · cases hwp
  · intro d f hf x hx ty ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      have hxm := hfv x hx
      subst hxm
      rw [hme ty ws hl] at hk
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.one pl, by simp⟩
    · simp at hf
  · intro d f x k n _ hx
    dsimp only at hx
    split at hx
    · cases hx
    · cases hx

/-! ## At `rodata`'s allocation -/

/-- `rodata`'s allocation is the term at which the layout keeps `m`'s
immediate. -/
theorem eB_eq : eB = SccCode.hello1Imm_t0 := rfl

/-- `rodata`'s allocation reads only `m`. -/
theorem eB_fv : ∀ x ∈ exprFv eB, x = "m" := by decide

/-- **A control at `rodata`'s allocation is placed**: `m` the immediate
`2`, `two` and `u` dead. -/
theorem placed_rdN {c : Ctl} (ht : c.term = eB) (he : c.env = envN) : Placed hello1Λ lbl s c := by
  refine ⟨fun x k => if x = "m" ∧ k = 0 then some (.imm 2) else none, ?_, ?_, ?_⟩
  · intro x ty ws hx k wd wp hwd hwp
    dsimp only at hwp
    split at hwp
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hwp
      rw [he] at hx
      simp [envN, TermRun.lookupE] at hx
      obtain ⟨-, rfl⟩ := hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
      subst hwd
      simp [WordPlaceRep, ValRep, TermRun.cst, Promises.TVal.mk0]
    · cases hwp
  · intro x hx ty ws hl k hk
    rw [ht] at hx
    have hxm : x = "m" := eB_fv x hx
    subst hxm
    rw [he] at hl
    simp [envN, TermRun.lookupE] at hl
    obtain ⟨-, rfl⟩ := hl
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    exact ⟨.imm 2, by simp⟩
  · intro x k n hx
    dsimp only at hx
    split at hx
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hx
      rw [ht, eB_eq]
      simp [hello1Λ, SccCode.hello1Imms]
    · cases hx

/-! ## `scc_rt_alloc`'s controls -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N Jc Jok Jslow Jfull)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
  {q : Call}

/-- **Every node of `scc_rt_alloc` is at the call's control or its hold.** -/
theorem ctl_of_N (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call) :
    ∀ i σ c, (N lab ms q i).J σ c → c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o := by
  intro i σ c h
  cases i <;> simp only [N, Jc, Jok, Jslow, Jfull] at h
  all_goals first
    | exact .inl h.1
    | exact .inl h.1.1
    | (obtain ⟨o, h⟩ := h; first | exact .inr ⟨o, h.1⟩ | exact .inr ⟨o, h.1.1⟩)
    | (rcases h with h | ⟨o, h⟩
       · exact .inl h.1
       · exact .inr ⟨o, h.1⟩)

/-- **A predicate of the call's controls holds at every node** of
`scc_rt_alloc`: `P` at every state whose memory a frame of the region
reaches from one of the frame condition, at the call's control or its
hold. -/
theorem allocW_of_ctl {P : Frag isaLSE2}
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) → P s c) :
    AllocW ms q P (fun _ _ => False) exe endPc R F := by
  have hN : ∀ i, NodeW P (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label ms q i) :=
    fun i s c ⟨_, _, _, _, σ, _, hF, hJ⟩ =>
      ⟨hP _ hF s c (DFrame.refl _ _) (ctl_of_N _ _ _ i σ c hJ), fun _ h => h⟩
  have hB : ∀ i blk, BlkW P (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label ms q i) blk :=
    fun i _ _ σ c _ _ _ _ _ hF hJ _ _ _ _ hD => ⟨hP _ hF _ c hD (ctl_of_N _ _ _ i σ c hJ), fun _ h => h⟩
  exact ⟨hB _ _, hB _ _, hB _ _, hN _, hN _, hB _ _, hN _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hN _,
    hN _, hB _ _, hN _, hB _ _, hN _⟩

/-- **Every node of `scc_rt_alloc` places the setup frame** in
`wc_rodata`'s call context (`RdPreW.alloc`'s frame condition, at
`MainPreW.rd`'s for the caller's state `m0`, `σC` of `scc_rt_main`'s region
`R`, the source at `rdJ'`'s): the call at `rdCN` (`placed_rdN`), `me` the
thread pointer in `scc_rt_main`'s cell `-80`, kept outside `wc_rodata`'s
and the allocator's regions (`framesPlaced_setup`). -/
theorem allocPlaced {g : MainG} {m0 : MachineData} {σC : AS} {e : Expr} {env : TermRun.Env} {w : TermRun.Word}
    (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hfv : ∀ y ∈ (exprFv e).filter (· != "r"), y = "me")
    (hme : ∀ ty ws, TermRun.lookupE env "me" = some (ty, ws) → ws = [w])
    (hw : w.val = .num g.tp.toBitVec.toNat) :
    AllocW ms q (fun s c => PlacedS hello1Λ lbl s c [setupFrame e env]) (fun _ _ => False) exe endPc (aR (mR R))
      (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) q m) := by
  refine allocW_of_ctl fun mA hFA s c hD hc => ?_
  obtain ⟨⟨-, hK, hA⟩, -, mC, σC', c1, -, ⟨⟨σe, ⟨-, hmc⟩, -, -⟩, -⟩, he, -⟩ := hFA
  obtain ⟨⟨σ0, ⟨hc1, -, -, hx0⟩, -, -, h80, -, -⟩, -⟩ := hmc
  have hq0 : q.c0 = rdCN := he.1.symm.trans hc1
  have hoff : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  obtain ⟨j, hj, hjv⟩ := hA.slot (-80) hoff
  have hkept := hK (-80) hoff fun ⟨_, _, h3⟩ => absurd h3 (by simp [Region.callee])
  have hb1 : (((mR R).base.toNat : Int)) = R.base.toNat + -80 :=
    Region.callee_base hR (by omega) (by decide) (by omega)
  have hok1 : (mR R).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hb2 : (((aR (mR R)).base.toNat : Int)) = (mR R).base.toNat + -48 :=
    Region.callee_base hok1 (by simp [mR, Region.callee]) (by decide) (by simp [mR, Region.callee])
  have ha := R.addr_toNat hR hoff
  have hhi2 : (aR (mR R)).hi = 0 := rfl
  have hload : Mem.loadInt s.st.1.dmem (R.addr (-80)) 8 = some j := by
    rw [hD _ (R.addr_fit hR hoff) (.inr (by omega)), hkept, hj]
  have hrep : WordPlaceRep (machine (kernel 1)) lbl s (.one (.slot (R.addr (-80)).toNat)) w.val := by
    rw [hw]; exact wpRep_slot hload (hjv.trans (h80.trans hx0))
  have hct : c.term = eB ∧ c.env = envN := by
    rcases hc with rfl | ⟨o, rfl⟩ <;> rw [hq0] <;> exact ⟨rfl, rfl⟩
  exact PlacedS.ofFrames (placed_rdN hct.1 hct.2) (framesPlaced_setup hfv hme hrep)

end Alloc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1W0.wpRep_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wpRep_slot

/--
info: 'Spike.Test.A64Hello1W0.framesPlaced_setup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms framesPlaced_setup

/--
info: 'Spike.Test.A64Hello1W0.placed_rdN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placed_rdN

/--
info: 'Spike.Test.A64Hello1W0.ctl_of_N' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ctl_of_N

/--
info: 'Spike.Test.A64Hello1W0.allocW_of_ctl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocW_of_ctl

/--
info: 'Spike.Test.A64Hello1W0.allocPlaced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocPlaced

end Spike.Test.A64Hello1W0
