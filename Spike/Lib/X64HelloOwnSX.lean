/-
**hello.w's main thread owning both TCB self words before the spawn** (x86-64 only; the hello counterpart of
`X64WakeOwnS`'s map, `X64WakeOwnT2`, `X64WakeOwnSW` and `X64WakeOwnT2W`): main's pre-spawn owned words are
hello's `ownGH` with main's TCB self word `T = tcbM L = pinA + 8` and the worker's `W = tcbWH L = pinA + 144`
appended where main holds them, so that the consumer's `OwnOk` of main's own map carries both words' latest
writes to the clone (`X64HelloSelfWords.SelfWordsAtClone`).

- `selfOwnH L s`: main owns `T` at `s`: on a pool stack from `scc_rt_start`'s `.x1` on, in `scc_rt_start` from
  `.x1` to `scc_rt_main`, or in `scc_rt_thread_init` after its self store (`.x8 + 48`, 3 bytes: from `.x8 + 51`
  up to `scc_rt_stack_take`).
- `ownSH`, `ownGHX L a s := ownGH L a s ++ ownSH L s`; `ownSH_congr`.
- `selfOwnWH L s`: main holds `W` at `s`: on a pool stack after the second `scc_rt_thread_init`'s self store, in
  `wc_main` from `.x25` (the second call's return) to `.stk` (past the clone, on the refused clone's path), or in
  the abort path entered from `.x27`.
- `tWH`, `ownSWH`, `ownGHXW L a s := ownGHX L a s ++ ownSWH L s`; `selfOwnWH_iff_off`, `ownSWH_congr_off`,
  `ownSWH_of_self`, `ownSWH_of_not`.
- `ownGH_addr`, `ownSH_disj`, `ownGHX_addr`, `tcbWH_notGHX`, `ownSWH_disj`: `ownGH`'s words are the counters and
  `a`; `T` is none of them (`PhRec.TcbSep`, `T ≠ a`) and `W` none of them nor `T` (`hW`).
- `appOkWH_of`, `appOkWH_none`: `AppOk` (`X64WakeOwnS.AppOk`, reused) of the appended `W`.
- `tcbWH_notG_W`: `hW` at `RuntimeLayout.ofPlaceWX`: `W` is A13's fifth spawn word, clear of the runtime's words
  and of `scc_rt_nthreads` (`X64WakeOwnSW.tcbSep_W`/`tcbM_ne_ntA_W` give `T`'s side).
- `tcbM_mem_ownGHXW`, `tcbWH_mem_ownGHXW`, `selfOwnWH_clone`, `clone_ownGHXW`: both words in `ownGHXW` at the clone
  (`.Lwc_main.x3 + 94`, `X64HelloClonePreH.cloneAtH`) on a pool stack;
  `selfWords_clone`: `SelfWordsAtClone` from `OwnOk` of `ownGHXW` there.

The generic pieces (`AppOk`, `SFactsSt.appendS`, `SFactsSt2.appendS`, `BlkW.appendS(2)`, `NodeW.appendS2`,
`ownTree_append`, `tcbM`, `tM`) are wake's, used as they are.

## Differences from the AArch64 version

AArch64 has no counterpart (its park and worker tail take the thread pointer from a register, so main owns no
TCB word). Against wake's x86-64 maps: hello's second TCB is at `pinA + 144` (wake: `pinA + 136`), A13's fifth
spawn word (wake: the fourth); `scc_rt_thread_init`'s self store is at `.x8 + 48` (wake: `.x7 + 48`); `W` is held
in `wc_main` from `.x25` to `.stk` and on the abort path from `.x27` (wake: `.x21`, `.x23`); the clone is at
`.Lwc_main.x3 + 94` (wake: `.x21 + 46`); the base map is hello's `ownGH` (`ownH`, `own2aH`, `own2bH`).
-/
import Spike.Lib.X64HelloSelfWords
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64HelloOwnLift
import Spike.Lib.X64WakeOwnT2W

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (inPc spPool raAt tcbM AppOk)
open Spike.Lib.X64HelloOwnLift (tcbWH tcbM_ne_tcbWH)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.Consumer1 (writeTree_mono)
open Spike.Lib.X64HelloSelfWords (SelfWordsAtClone)

/-! ## Main's TCB word -/

/-- **Main owns `tcbM` at `s`**: on a pool stack at a pc from `scc_rt_start`'s `.x1` on, in `scc_rt_start` from
`.x1` to `scc_rt_main`, or in `scc_rt_thread_init` after its self store (`.x8 + 51` up to
`scc_rt_stack_take`). -/
def selfOwnH (L : RuntimeLayout) (s : State) : Prop :=
  (spPool L s ∧ (L.lab ".Lscc_rt_start.x1").toBitVec.toNat ≤ pcOf s) ∨
    inPc L ".Lscc_rt_start.x1" "scc_rt_main" s ∨
    ((L.lab ".Lscc_rt_thread_init.x0").toBitVec.toNat + 51 ≤ pcOf s ∧
      pcOf s < (L.lab "scc_rt_stack_take").toBitVec.toNat)

instance (L : RuntimeLayout) (s : State) : Decidable (selfOwnH L s) := by
  unfold selfOwnH; infer_instance

/-- **Main's own TCB word**, owned holding its address where `selfOwnH`. -/
def ownSH (L : RuntimeLayout) (s : State) : List (Loc × Val) :=
  if selfOwnH L s then [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] else []

/-- **Main's owned words with its TCB word**: `ownGH`'s and `tcbM`. -/
def ownGHX (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  ownGH L a s ++ ownSH L s

/-- **`ownSH` reads the pc and `%rsp` only.** -/
theorem ownSH_congr {L : RuntimeLayout} {s s' : State} (hpc : pcOf s' = pcOf s)
    (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp) : ownSH L s' = ownSH L s := by
  have h : selfOwnH L s' ↔ selfOwnH L s := by unfold selfOwnH spPool inPc; rw [hpc, hsp]
  unfold ownSH; simp only [h]

/-- `ownSH` at a `selfOwnH` state. -/
theorem ownSH_of_self {L : RuntimeLayout} {s : State} (h : selfOwnH L s) :
    ownSH L s = [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] := by
  unfold ownSH; simp [h]

/-- `ownSH` off `selfOwnH`. -/
theorem ownSH_of_not {L : RuntimeLayout} {s : State} (h : ¬ selfOwnH L s) : ownSH L s = [] := by
  unfold ownSH; simp [h]

/-! ## The worker's TCB word -/

/-- The worker's TCB self word, holding its address. -/
abbrev tWH (L : RuntimeLayout) : List (Loc × Val) := [(⟨tcbWH L, 8⟩, (tcbWH L).setWidth 128)]

/-- **Main holds `tcbWH` at `s`**: on a pool stack after the second `scc_rt_thread_init`'s self store
(`.x8 + 51` up to `scc_rt_stack_take`), in `wc_main` from `.x25` to `.stk`, or in the abort path entered from
`.x27`. -/
def selfOwnWH (L : RuntimeLayout) (s : State) : Prop :=
  (spPool L s ∧ (L.lab ".Lscc_rt_thread_init.x0").toBitVec.toNat + 51 ≤ pcOf s ∧
      pcOf s < (L.lab "scc_rt_stack_take").toBitVec.toNat) ∨
    inPc L ".Lwc_main.x3" ".Lwc_main.stk" s ∨
    (inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAt L ".Lwc_main.x5" s)

instance (L : RuntimeLayout) (s : State) : Decidable (selfOwnWH L s) := by
  unfold selfOwnWH; infer_instance

/-- **The worker's TCB word**, held holding its address where `selfOwnWH`. -/
def ownSWH (L : RuntimeLayout) (s : State) : List (Loc × Val) :=
  if selfOwnWH L s then tWH L else []

/-- **Main's owned words before the spawn**: `ownGHX`'s and the worker's TCB word. -/
def ownGHXW (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  ownGHX L a s ++ ownSWH L s

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Marks} {s : State}

/-- **`selfOwnWH` off the abort path** reads the pc and `%rsp` only. -/
theorem selfOwnWH_iff_off {s' : State} (hpc : pcOf s' = pcOf s) (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp)
    (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) : selfOwnWH L s' ↔ selfOwnWH L s := by
  have hi : ∀ l₁ l₂, inPc L l₁ l₂ s' ↔ inPc L l₁ l₂ s := fun _ _ => by unfold inPc; rw [hpc]
  have hab' : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s' := fun h => hab ((hi _ _).mp h)
  have hp : spPool L s' ↔ spPool L s := by unfold spPool; rw [hsp]
  unfold selfOwnWH
  simp only [hab, hab', false_and, or_false, hi, hp, hpc]

/-- **`ownSWH` off the abort path** reads the pc and `%rsp` only. -/
theorem ownSWH_congr_off {s' : State} (hpc : pcOf s' = pcOf s) (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp)
    (hab : ¬ inPc L "scc_rt_abort" "scc_rt_thr_worker" s) : ownSWH L s' = ownSWH L s := by
  unfold ownSWH; simp only [selfOwnWH_iff_off hpc hsp hab]

/-- `ownSWH` at a `selfOwnWH` state. -/
theorem ownSWH_of_self (h : selfOwnWH L s) : ownSWH L s = tWH L := by
  unfold ownSWH; simp [h]

/-- `ownSWH` off `selfOwnWH`. -/
theorem ownSWH_of_not (h : ¬ selfOwnWH L s) : ownSWH L s = [] := by
  unfold ownSWH; simp [h]

/-! ## The words off each other -/

/-- **`ownGH`'s words** are the four counters and `a`. -/
theorem ownGH_addr {l : Loc} {w : Val} (h : (l, w) ∈ ownGH L a s) :
    l.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a] := by
  let Q : List (Loc × Val) → Prop := fun xs => ∀ p ∈ xs, p.1.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a]
  have hV : ∀ pb pa xb xa nb na i, Q (Spike.Lib.X64.WakePh.ownV L a pb pa xb xa nb na i) := by
    intro _ _ _ _ _ _ _ p hm
    simp only [Spike.Lib.X64.WakePh.ownV, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp
  have hW : ∀ i, Q (ownH L a i) := fun i => by
    show Q (Spike.Lib.X64.WakePh.ownW L a i); rw [Spike.Lib.X64.WakePh.ownW_eq]; exact hV _ _ _ _ _ _ _
  have hI : ∀ (c : Prop) [Decidable c] (x y : List (Loc × Val)), Q x → Q y → Q (if c then x else y) := by
    intro c _ x y hx hy; split <;> assumption
  have h2a : ∀ i, Q (own2aH L a i) := fun _ => hV _ _ _ _ _ _ _
  have h2b : ∀ i, Q (own2bH L a i) := fun _ => hV _ _ _ _ _ _ _
  have hG : Q (ownGH L a s) := by
    unfold ownGH
    exact hI _ _ _ (hI _ _ _ (h2a _) (hW _)) (hI _ _ _ (hI _ _ _ (h2b _) (hW _)) (hI _ _ _ (h2a _)
      (hI _ _ _ (h2b _) (hI _ _ _ (hI _ _ _ (h2a _) (hI _ _ _ (h2b _) (hW _))) (hW _)))))
  exact hG (l, w) h

/-- **`ownSH`'s words are off `ownGH`'s**, `tcbM` off the counters and `a`. -/
theorem ownSH_disj (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) :
    ∀ l w w', (l, w) ∈ ownSH L s → (l, w') ∉ ownGH L a s := by
  intro l w w' hm hg
  have h1 := ownGH_addr hg
  unfold ownSH at hm
  split at hm
  · obtain ⟨rfl, -⟩ := List.mem_singleton.mp hm
    have h2 := Spike.Lib.X64.WakePh.tcbM_sep hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 h2
    rcases h1 with h | h | h | h | h
    · exact h2 (.inl h)
    · exact h2 (.inr (.inl h))
    · exact h2 (.inr (.inr (.inl h)))
    · exact h2 (.inr (.inr (.inr h)))
    · exact ha h
  · simp at hm

/-- **`ownGHX`'s words** are the four counters, `a` and `tcbM`. -/
theorem ownGHX_addr {l : Loc} {w : Val} (h : (l, w) ∈ ownGHX L a s) :
    l.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a, tcbM L] := by
  rcases List.mem_append.mp h with h | h
  · have h1 := ownGH_addr h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 ⊢
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;> simp [h1]
  · unfold ownSH at h
    split at h
    · obtain ⟨rfl, -⟩ := List.mem_singleton.mp h
      simp
    · simp at h

/-- **`tcbWH` is none of `ownGHX`'s words**, given it is none of the counters and `a` (`hW`). -/
theorem tcbWH_notGHX (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (s : State) :
    ∀ w, ((⟨tcbWH L, 8⟩ : Loc), w) ∉ ownGHX L a s := by
  intro w hm
  have h1 := ownGHX_addr hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 hW
  rcases h1 with h | h | h | h | h | h
  · exact hW (.inl h)
  · exact hW (.inr (.inl h))
  · exact hW (.inr (.inr (.inl h)))
  · exact hW (.inr (.inr (.inr (.inl h))))
  · exact hW (.inr (.inr (.inr (.inr h))))
  · exact tcbM_ne_tcbWH L h.symm

/-- **`ownSWH`'s words are off `ownGHX`'s.** -/
theorem ownSWH_disj (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    ∀ l w w', (l, w) ∈ ownSWH L s → (l, w') ∉ ownGHX L a s := by
  intro l w w' hm
  unfold ownSWH at hm
  split at hm
  · obtain ⟨rfl, -⟩ := List.mem_singleton.mp hm
    exact tcbWH_notGHX hW s w'
  · simp at hm

/-! ## `AppOk` of the worker's word -/

/-- **`AppOk` from `selfOwnWH` constant and no write to `tcbWH`'s word**: the successors `selfOwnWH` as `s` does
(`hsucc`), a non-syscall instruction writes no `⟨tcbWH, 8⟩` (`hw`), `tcbWH` off the counters and `a` (`hW`). -/
theorem appOkWH_of (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hsucc : ∀ s', StSucc μ s s' → (selfOwnWH L s' ↔ selfOwnWH L s))
    (hw : abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => l ≠ ⟨tcbWH L, 8⟩) tree) :
    AppOk μ (ownGHX L a) (ownSWH L) s := by
  refine ⟨fun s' h => ?_, fun hns tree he => ?_, ownSWH_disj hW⟩
  · unfold ownSWH; simp only [hsucc s' h]
  · refine writeTree_mono (fun l _ hl w hm => ?_) (hw hns tree he)
    unfold ownSWH at hm
    split at hm
    · exact hl (List.mem_singleton.mp hm |> congrArg Prod.fst)
    · simp at hm

/-- **`AppOk` off `selfOwnWH`**: neither `s` nor any successor `selfOwnWH`s, no write condition. -/
theorem appOkWH_none (hn : ¬ selfOwnWH L s) (hsucc : ∀ s', StSucc μ s s' → ¬ selfOwnWH L s') :
    AppOk μ (ownGHX L a) (ownSWH L) s := by
  have h0 := ownSWH_of_not hn
  refine ⟨fun s' h => ?_, fun _ tree _ => ?_, fun l w w' hm => ?_⟩
  · rw [h0, ownSWH_of_not (hsucc s' h)]
  · exact writeTree_mono (fun l v _ w hm => by rw [h0] at hm; simp at hm) (Spike.Lib.Consumer1.writeTree_true tree)
  · rw [h0] at hm; simp at hm

/-! ## At a placed output -/

section Placed

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (h : Spike.Lib.PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

private theorem ne_of_sepH {a b : BitVec 64} (hs : Scc.Cert.Rt.X64.WordSep a b) : a ≠ b := fun he => by
  subst he; unfold Scc.Cert.Rt.X64.WordSep at hs; omega

/-- **`tcbWH` is a spawn word** (A13's `spawnWords`, index 4: `80 + 8 * 4 = 112`). -/
theorem tcbWH_mem_spawnWords (L : RuntimeLayout) : tcbWH L ∈ Scc.Cert.Spawn.X64.spawnWords L.pinA := by
  unfold Scc.Cert.Spawn.X64.spawnWords
  exact List.mem_map.mpr ⟨4, List.mem_range.mpr (by decide), rfl⟩

/-- **The worker's TCB word is none of the counters nor `scc_rt_nthreads`** at `ofPlaceWX`, given A13's data part
(as `X64WakeOwnT2W.tcb2_notG_W` at index 4). -/
theorem tcbWH_notG_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    tcbWH (Ly) ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab] := by
  have hnt := Spike.Lib.X64.WakePh.ntA_W h i hA13
  have hm := tcbWH_mem_spawnWords (Ly)
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
  obtain ⟨⟨⟨⟨⟨-, -⟩, hold⟩, -⟩, hpw⟩, -⟩ := hA13
  have hsep : ∀ b ∈ (Ly).rtWords, Scc.Cert.Rt.X64.WordSep (tcbWH (Ly)) b := by
    intro b hb
    have := List.all_eq_true.mp hold (tcbWH (Ly)) (List.mem_cons_of_mem _ hm)
    exact of_decide_eq_true (List.all_eq_true.mp this b hb)
  have hnt' : tcbWH (Ly) ≠ Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab := by
    rw [hnt]
    exact (ne_of_sepH ((List.pairwise_cons.mp hpw).1 _ hm)).symm
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
  exact ⟨ne_of_sepH (hsep _ (Ly).pn_mem), ne_of_sepH (hsep _ (Ly).lock_mem),
    ne_of_sepH (hsep _ (Ly).freeN_mem), ne_of_sepH (hsep _ (Ly).next_mem), hnt'⟩

end Placed

/-! ## Both self words at the clone -/

/-- **`ownGHXW` holds `tcbWH`** with its address at a `selfOwnWH` state. -/
theorem tcbWH_mem_ownGHXW (h : selfOwnWH L s) : (⟨tcbWH L, 8⟩, (tcbWH L).setWidth 128) ∈ ownGHXW L a s := by
  unfold ownGHXW; rw [ownSWH_of_self h]; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **`ownGHXW` holds `tcbM`** with its address at a `selfOwnH` state. -/
theorem tcbM_mem_ownGHXW (h : selfOwnH L s) : (⟨tcbM L, 8⟩, (tcbM L).setWidth 128) ∈ ownGHXW L a s := by
  unfold ownGHXW ownGHX
  rw [ownSH_of_self h]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- A resolved label of the hello cells. -/
private theorem labVH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo helloCells l = some y) : L.lab l = Int64.ofNat y :=
  hlab _ _ (by rw [← codeT_eq]; exact h)

/-- **`selfOwnWH` at the clone's `syscall`** (`.Lwc_main.x3 + 94`, `X64HelloClonePreH.cloneAtH`). -/
theorem selfOwnWH_clone (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hpc : s.st.2 = L.lab ".Lwc_main.x3" + 94) : selfOwnWH L s := by
  have e25 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203812 := labVH hlab (by decide +kernel)
  have eS : L.lab ".Lwc_main.stk" = Int64.ofNat 4203986 := labVH hlab (by decide +kernel)
  refine .inr (.inl ?_)
  unfold inPc pcOf
  rw [hpc, e25, eS]
  decide

/-- **The clone agreement for both self words**: at the clone's `syscall` on a pool stack, `ownGHXW L a s` holds
`tcbM` and `tcbWH`, each with its address (`post_startOXW`'s `hT0`, `hW0` at `own₀ = ownGHXW L a s`). -/
theorem clone_ownGHXW (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsp : spPool L s) (hpc : s.st.2 = L.lab ".Lwc_main.x3" + 94) :
    (⟨tcbM L, 8⟩, (tcbM L).setWidth 128) ∈ ownGHXW L a s ∧
      (⟨tcbWH L, 8⟩, (tcbWH L).setWidth 128) ∈ ownGHXW L a s :=
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := labVH hlab (by decide +kernel)
  have e25 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203812 := labVH hlab (by decide +kernel)
  have hx : (L.lab ".Lscc_rt_start.x1").toBitVec.toNat ≤ pcOf s := by
    unfold pcOf; rw [hpc, e1, e25]; decide
  ⟨tcbM_mem_ownGHXW (.inl ⟨hsp, hx⟩), tcbWH_mem_ownGHXW (selfOwnWH_clone hlab hpc)⟩

/-- **The two self words at the clone** (`X64HelloSelfWords.SelfWordsAtClone`): from the consumer's `OwnOk` of
main's pre-spawn own map `ownGHXW L a s` at the clone's `syscall` on a pool stack. -/
theorem selfWords_clone (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsp : spPool L s) (hpc : s.st.2 = L.lab ".Lwc_main.x3" + 94) {mem : Memory} {prom : List Time}
    (hown : Spike.Lib.ExtRows.OwnOk (ownGHXW L a s) mem prom) : SelfWordsAtClone mem prom (tcbM L) (tcbWH L) :=
  SelfWordsAtClone.of_ownOk hown (clone_ownGHXW hlab hsp hpc).1 (clone_ownGHXW hlab hsp hpc).2

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.ownSH_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownSH_congr

/-- info: 'Spike.Lib.X64.HelloPh.ownSWH_congr_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownSWH_congr_off

/-- info: 'Spike.Lib.X64.HelloPh.ownSH_disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownSH_disj

/-- info: 'Spike.Lib.X64.HelloPh.ownSWH_disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ownSWH_disj

/-- info: 'Spike.Lib.X64.HelloPh.appOkWH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.appOkWH_of

/-- info: 'Spike.Lib.X64.HelloPh.appOkWH_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.appOkWH_none

/-- info: 'Spike.Lib.X64.HelloPh.tcbWH_notG_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tcbWH_notG_W

/-- info: 'Spike.Lib.X64.HelloPh.clone_ownGHXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.clone_ownGHXW

/-- info: 'Spike.Lib.X64.HelloPh.selfWords_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.selfWords_clone
