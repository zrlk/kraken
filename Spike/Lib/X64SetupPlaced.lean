/-
**The setup call's frame placed, at any layout** (x86-64): the generic
parts of `Spike/Test/X64Hello1PlacedS.lean`, for any program with a setup
block. While `rodata` runs, the only suspended frame is the one its call
from `SrcSem.setupTerm` pushed: it returns into `r` and continues with
`SrcCalls.setupCont` (pair `r` with `me`, enter `main`), so it reads `me`
alone. The thread word `me` is placed where `scc_rt_main` keeps the
thread pointer (a register before it saves it, its slot after), the
source's `meW` that number (the start picks it, `NJLS.meNum`).

- `wpRep_slot`: a word at a mapped 8-byte address represents its number.
- `framesPlaced_me`: a single frame whose body reads no variable but `me`
  (besides its binder), `me` one word represented at a place, is placed.
- `framesPlaced_setupCont`: the frame of the setup call, at any
  environment binding `me` to one word.
- `ctl_of_N`, `allocW_of_ctl`: every node of `scc_rt_alloc` is at the
  call's control or its hold; a predicate of such controls at every memory
  the node's frame condition and a frame of its region reach holds at every
  node.
- `allocPlacedS`: every node of `scc_rt_alloc` places the current control
  and the frames, given both at the call's controls (`PlacedS.ofFrames`).
-/
import Spike.Lib.X64PlacedS
import Spike.Lib.X64Alloc
import Spike.Lib.Src.SetupFrame

namespace Spike.Lib.X64SetupPlaced

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide Ctl Frag)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW DFrame holdCtr)
open Spike.Lib.X64ConsumerS (PlacedS FramesPlaced)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## The setup frame -/

/-- **A word at a mapped address represents its number**: the 8 bytes at
`a` load `j`, of bits `t`. -/
theorem wpRep_slot {a : BitVec 64} {j : Int} {t : BitVec 64} (h : Mem.loadInt s.st.1.dmem a 8 = some j)
    (ht : BitVec.ofInt 64 j = t) :
    WordPlaceRep (machine (kernel 1)) lbl s (.one (.slot a.toNat)) (.num t.toNat) := by
  refine ⟨t.toNat, ?_, t.isLt, rfl⟩
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = some t.toNat
  simp [Scc.Sem.X64.privLoad, h, ht]

/-- **A frame reading only `me` is placed**, `me` one word `w` represented
at the place `pl`. -/
theorem framesPlaced_me {fr : TermRun.Frame} {w : TermRun.Word} {pl : Place (machine (kernel 1)).I.RegId}
    (hfv : ∀ y ∈ (exprFv fr.body).filter (· != fr.x), y = "me")
    (hme : ∀ ty ws, TermRun.lookupE fr.env "me" = some (ty, ws) → ws = [w])
    (hrep : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    FramesPlaced Λ lbl s [fr] := by
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

/-- **The setup call's frame is placed**: returning into `r` and then
`setupCont`, at any environment binding `me` to one word `w` represented at
`pl`. -/
theorem framesPlaced_setupCont {env : TermRun.Env} {σs : List Ty} {τ : Ty} {w : TermRun.Word}
    {pl : Place (machine (kernel 1)).I.RegId}
    (hme : ∀ ty ws, TermRun.lookupE env "me" = some (ty, ws) → ws = [w])
    (hrep : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    FramesPlaced Λ lbl s [⟨"r", SrcCalls.setupCont, env, σs, τ⟩] :=
  framesPlaced_me Src.setupCont_fv hme hrep

/-! ## `scc_rt_alloc`'s controls -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N Jc Jok Jslow Jfull)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
  {q : Call}

/-- **Every node of `scc_rt_alloc` is at the call's control or its hold.** -/
theorem ctl_of_N (lab : Label → Int64) (ms : MemSide isa) (q : Call) :
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
theorem allocW_of_ctl {P : Frag isa}
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) → P s c) :
    AllocW ms q P (fun _ _ => False) exe endPc R F := by
  have hN : ∀ i, NodeW P (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label ms q i) :=
    fun i s c ⟨_, _, _, _, σ, _, hF, hJ⟩ =>
      ⟨hP _ hF s c (DFrame.refl _ _) (ctl_of_N _ _ _ i σ c hJ), fun _ h => h⟩
  have hB : ∀ i blk, BlkW P (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label ms q i) blk :=
    fun i _ _ σ c _ _ _ _ _ hF hJ _ _ _ _ hD => ⟨hP _ hF _ c hD (ctl_of_N _ _ _ i σ c hJ), fun _ h => h⟩
  exact ⟨hB _ _, hB _ _, hB _ _, hN _, hB _ _, hN _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hN _,
    hB _ _, hN _, hB _ _, hN _, hB _ _, hN _, hB _ _, hN _, hB _ _, hN _, hB _ _, hN _, hB _ _,
    hN _, hB _ _, hN _, hB _ _, hN _⟩

/-- **Every node of `scc_rt_alloc` places its control and the frames `fs`**,
given both at every state a frame of the region reaches from the frame
condition, at the call's control or its hold. -/
theorem allocPlacedS {fs : List TermRun.Frame}
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs) :
    AllocW ms q (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F :=
  allocW_of_ctl fun m0 hF s c hD hc =>
    let h := hP m0 hF s c hD hc
    Spike.Lib.X64ConsumerS.PlacedS.ofFrames h.1 h.2

end Alloc

/--
info: 'Spike.Lib.X64SetupPlaced.framesPlaced_setupCont' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms framesPlaced_setupCont

/--
info: 'Spike.Lib.X64SetupPlaced.allocPlacedS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocPlacedS

end Spike.Lib.X64SetupPlaced
