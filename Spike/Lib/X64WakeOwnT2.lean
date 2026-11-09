/-
**Main holding the worker's TCB word before the spawn** (x86-64; X64-OwnW
part 2): main's second `scc_rt_thread_init` call (from
`wc_main`'s `.x20`, on a pool stack) writes the worker's TCB self word
`tcb2 = pinA + 104` (`Tcb2Call.tcb2Q_tcbOf`) at its first store
(`movq %rax, (%rcx)` at `.x7 + 48`). From then on main holds it, holding its
address, up to its `clone` (`.Lwc_main.x3 + 46`), whose own list `own₀`
must hold it for `X64WakeSpawn.spawn_ofXW` (`hW0`, the hand-over to the
worker). This file appends it to `ownGX` (`ownGXW`), as `X64WakeOwnS`
appends `tcbM` to `ownG`.

- `tcb2`: the worker's TCB word; `tcb2_ne_tcbM`.
- `selfOwnW L s`: main holds `tcb2` at `s`: on a pool stack from `.x7 + 51`
  (after the store) to `scc_rt_stack_take` (the rest of the second
  `scc_rt_thread_init`); in `wc_main` from `.x21` to `.stk` (up to the
  `clone`, and on the refused clone's path); in the abort path entered from
  that path (`raAt .x23`, where `ownG` picks `own2b`).
- `ownSW`, `ownGXW L a s := ownGX L a s ++ ownSW L s`; `ownSW_congr_off`.
- `ownGX_addr`, `tcb2_notGX`, `ownSW_disj`: `ownGX`'s words are the
  counters, `a` and `tcbM`; `tcb2` is none of them given it is none of the
  counters and `a` (`hW`; at wake's layout from A13's data part,
  `X64WakeOwnT2W.tcb2_notG_W`).
- `appOkW_of`, `appOkW_none`, `selfOwnW_iff_off`: the `AppOk` of the
  appended word (`SFactsSt2.appendS`, `BlkW.appendS2`, `NodeW.appendS2` at
  `own := ownGX L a`).
- `tcb2_mem_ownGXW`, `tcbM_mem_ownGXW`, `selfOwnW_clone`, `clone_ownGXW`:
  both self words in `ownGXW` at the clone (`hT0`, `hW0` of
  `spawn_ofXW` at `own₀ = ownGXW L a s`).

**Deviations.** The held range runs past the `clone` (to `.stk`, and the
abort path at `raAt .x23`) because the `syscall`'s refused results resume
main in that range under the same state facts (`ownSys` keeps the owned
words across every `certSuccs` result); the abort path's selection reads the
return address word, as `ownG`'s does, so `AppOk` there needs `raAt` kept
(`ownSW_congr_off` covers the pcs off the abort path only).
-/
import Spike.Lib.X64WakeOwnPark
import Spike.Lib.X64WakeOwnS

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.Consumer1 (writeTree_mono writeTree_true)

/-! ## The worker's TCB word -/

/-- **The worker's TCB word** `scc_rt_pinned + 104` (the second
`scc_rt_alloc_tcb` call's, `Tcb2Call.tcb2Q_tcbOf`). -/
abbrev tcb2 (L : RuntimeLayout) : BitVec 64 := L.pinA + 136#64

/-- The two TCB words differ. -/
theorem tcb2_ne_tcbM (L : RuntimeLayout) : tcb2 L ≠ tcbM L := by
  intro h; bv_omega

/-! ## The appended word -/

/-- **Main holds `tcb2` at `s`**: on a pool stack after the second
`scc_rt_thread_init`'s first store (`.x7 + 51` up to `scc_rt_stack_take`),
in `wc_main` from `.x21` to `.stk`, or in the abort path entered from
`.x23`. -/
def selfOwnW (L : RuntimeLayout) (s : State) : Prop :=
  (spPool L s ∧ (L.lab ".Lscc_rt_thread_init.x0").toBitVec.toNat + 51 ≤ pcOf s ∧
      pcOf s < (L.lab "scc_rt_stack_take").toBitVec.toNat) ∨
    inPc L ".Lwc_main.x3" ".Lwc_main.stk" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lwc_main.x5" s)

instance (L : RuntimeLayout) (s : State) : Decidable (selfOwnW L s) := by
  unfold selfOwnW; infer_instance

/-- **The worker's TCB word**, held holding its address where `selfOwnW`. -/
def ownSW (L : RuntimeLayout) (s : State) : List (Loc × Val) :=
  if selfOwnW L s then [(⟨tcb2 L, 8⟩, (tcb2 L).setWidth 128)] else []

/-- **Main's owned words before the spawn**: `ownGX`'s and the worker's
TCB word. -/
def ownGXW (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  ownGX L a s ++ ownSW L s

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Marks} {s : State}

/-- **`selfOwnW` off the abort path** reads the pc and `%rsp` only. -/
theorem selfOwnW_iff_off {s' : State} (hpc : pcOf s' = pcOf s) (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp)
    (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) : selfOwnW L s' ↔ selfOwnW L s := by
  have hi : ∀ l₁ l₂, inPc L l₁ l₂ s' ↔ inPc L l₁ l₂ s := fun _ _ => by unfold inPc; rw [hpc]
  have hab' : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s' := fun h => hab ((hi _ _).mp h)
  have hp : spPool L s' ↔ spPool L s := by unfold spPool; rw [hsp]
  unfold selfOwnW
  simp only [hab, hab', false_and, or_false, hi, hp, hpc]

/-- **`ownSW` off the abort path** reads the pc and `%rsp` only. -/
theorem ownSW_congr_off {s' : State} (hpc : pcOf s' = pcOf s) (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp)
    (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) : ownSW L s' = ownSW L s := by
  unfold ownSW; simp only [selfOwnW_iff_off hpc hsp hab]

/-- `ownSW` at a `selfOwnW` state. -/
theorem ownSW_of_self (h : selfOwnW L s) : ownSW L s = [(⟨tcb2 L, 8⟩, (tcb2 L).setWidth 128)] := by
  unfold ownSW; simp [h]

/-- `ownSW` off `selfOwnW`. -/
theorem ownSW_of_not (h : ¬ selfOwnW L s) : ownSW L s = [] := by
  unfold ownSW; simp [h]

/-! ## `tcb2` off `ownGX`'s words -/

/-- **`ownGX`'s words** are the four counters, `a` and `tcbM`. -/
theorem ownGX_addr {l : Loc} {w : Val} (h : (l, w) ∈ ownGX L a s) :
    l.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a, tcbM L] := by
  rcases List.mem_append.mp h with h | h
  · have h1 := ownG_addr h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 ⊢
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;> simp [h1]
  · unfold ownS at h
    split at h
    · obtain ⟨rfl, -⟩ := List.mem_singleton.mp h
      simp
    · simp at h

/-- **`tcb2` is none of `ownGX`'s words**, given it is none of the counters
and `a` (`hW`). -/
theorem tcb2_notGX (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (s : State) :
    ∀ w, ((⟨tcb2 L, 8⟩ : Loc), w) ∉ ownGX L a s := by
  intro w hm
  have h1 := ownGX_addr hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 hW
  rcases h1 with h | h | h | h | h | h
  · exact hW (.inl h)
  · exact hW (.inr (.inl h))
  · exact hW (.inr (.inr (.inl h)))
  · exact hW (.inr (.inr (.inr (.inl h))))
  · exact hW (.inr (.inr (.inr (.inr h))))
  · exact tcb2_ne_tcbM L h

/-- **`ownSW`'s words are off `ownGX`'s.** -/
theorem ownSW_disj (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    ∀ l w w', (l, w) ∈ ownSW L s → (l, w') ∉ ownGX L a s := by
  intro l w w' hm
  unfold ownSW at hm
  split at hm
  · obtain ⟨rfl, -⟩ := List.mem_singleton.mp hm
    exact tcb2_notGX hW s w'
  · simp at hm

/-! ## `AppOk` of the appended word -/

/-- **`AppOk` from `selfOwnW` constant and no write to `tcb2`'s word**: the
successors `selfOwnW` as `s` does (`hsucc`), a non-syscall instruction
writes no `⟨tcb2, 8⟩` (`hw`), `tcb2` off the counters and `a` (`hW`). -/
theorem appOkW_of (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hsucc : ∀ s', StSucc μ s s' → (selfOwnW L s' ↔ selfOwnW L s))
    (hw : abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => l ≠ ⟨tcb2 L, 8⟩) tree) :
    AppOk μ (ownGX L a) (ownSW L) s := by
  refine ⟨fun s' h => ?_, fun hns tree he => ?_, ownSW_disj hW⟩
  · unfold ownSW; simp only [hsucc s' h]
  · refine writeTree_mono (fun l _ hl w hm => ?_) (hw hns tree he)
    unfold ownSW at hm
    split at hm
    · exact hl (List.mem_singleton.mp hm |> congrArg Prod.fst)
    · simp at hm

/-- **`AppOk` off `selfOwnW`**: neither `s` nor any successor `selfOwnW`s,
no write condition. -/
theorem appOkW_none (hn : ¬ selfOwnW L s) (hsucc : ∀ s', StSucc μ s s' → ¬ selfOwnW L s') :
    AppOk μ (ownGX L a) (ownSW L) s := by
  have h0 := ownSW_of_not hn
  refine ⟨fun s' h => ?_, fun _ tree _ => ?_, fun l w w' hm => ?_⟩
  · rw [h0, ownSW_of_not (hsucc s' h)]
  · exact writeTree_mono (fun l v _ w hm => by rw [h0] at hm; simp at hm) (writeTree_true tree)
  · rw [h0] at hm; simp at hm

/-! ## Both self words at the clone -/

/-- **`ownGXW` holds `tcb2`** with its address at a `selfOwnW` state. -/
theorem tcb2_mem_ownGXW (h : selfOwnW L s) : (⟨tcb2 L, 8⟩, (tcb2 L).setWidth 128) ∈ ownGXW L a s := by
  unfold ownGXW; rw [ownSW_of_self h]; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **`ownGXW` holds `tcbM`** with its address at a `selfOwn` state. -/
theorem tcbM_mem_ownGXW (h : selfOwn L s) : (⟨tcbM L, 8⟩, (tcbM L).setWidth 128) ∈ ownGXW L a s :=
  List.mem_append_left _ (tcbM_mem_ownGX h)

/-- A resolved label of the wake cells. -/
private theorem labV (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo wakeCells l = some y) : L.lab l = Int64.ofNat y :=
  hlab _ _ (by rw [← codeT_eq]; exact h)

/-- **`selfOwnW` at the clone's `syscall`** (`.Lwc_main.x3 + 46`,
`X64WakePreA.cloneAt`). -/
theorem selfOwnW_clone (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hpc : s.st.2 = L.lab ".Lwc_main.x3" + 46) : selfOwnW L s := by
  have e21 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203435 := labV hlab (by decide +kernel)
  have eS : L.lab ".Lwc_main.stk" = Int64.ofNat 4203552 := labV hlab (by decide +kernel)
  refine .inr (.inl ?_)
  unfold inPc pcOf
  rw [hpc, e21, eS]
  decide

/-- **The clone agreement for both self words**: at the clone's `syscall`
on a pool stack, `ownGXW L a s` holds `tcbM` and `tcb2`, each with its
address (`spawn_ofXW`'s `hT0`, `hW0` at `own₀ = ownGXW L a s`). -/
theorem clone_ownGXW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsp : spPool L s) (hpc : s.st.2 = L.lab ".Lwc_main.x3" + 46) :
    (⟨tcbM L, 8⟩, (tcbM L).setWidth 128) ∈ ownGXW L a s ∧
      (⟨tcb2 L, 8⟩, (tcb2 L).setWidth 128) ∈ ownGXW L a s :=
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := labV hlab (by decide +kernel)
  have e21 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203435 := labV hlab (by decide +kernel)
  have hx : (L.lab ".Lscc_rt_start.x1").toBitVec.toNat ≤ pcOf s := by
    unfold pcOf; rw [hpc, e1, e21]; decide
  ⟨tcbM_mem_ownGXW (.inl ⟨hsp, hx⟩), tcb2_mem_ownGXW (selfOwnW_clone hlab hpc)⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcb2_ne_tcbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb2_ne_tcbM

/-- info: 'Spike.Lib.X64.WakePh.ownSW_congr_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownSW_congr_off

/-- info: 'Spike.Lib.X64.WakePh.ownSW_disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownSW_disj

/-- info: 'Spike.Lib.X64.WakePh.appOkW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.appOkW_of

/-- info: 'Spike.Lib.X64.WakePh.appOkW_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.appOkW_none

/-- info: 'Spike.Lib.X64.WakePh.clone_ownGXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.clone_ownGXW
