/-
**The `treiber2` regression of the framed (c′) spec**
(AArch64).

The earlier prototype's `t2_obl`/`t2_step` reduced `treiber2`
to two whole-program obligations over a per-position table. Here the same
shape is rebuilt from the framed pieces (`Lin/Frame.lean`):

- the layout `t2L t nd` (`top` at `t`, thread `w`'s node `nd w`, link word
  `⟨n+8, 8⟩`; the 4-byte data word is **client data**, not a node word);
- the fragments `pushF` (positions `3..8`, entry `3`, exit `10`) and `popF`
  (positions `10..16`, entry `10`, exits `17`/`21`) of any program with the
  `treiber2` cells (`TermTreiber2P.Cells W σ true`);
- the client invariant `t2CI` (static state, position facts, `X1 = nd w`,
  no committed own entry before the push) and **`t2_clientRely`, proved**:
  the client code (data store `1`, `MOV X10,X2` `17`, data load `18`,
  `B done` `19`, halt `21`) respects the rely;
- `t2_obl`/`t2_step`: the lifting's obligations and the per-step relation
  on the fuel-free machine, with **only** `PushFragObl`/`PopFragObl` open. The
  fuel-indexed and executable forms are the generic corollaries
  `RelLift.Obl.stepSem`/`Obl.reachSem`/`Obl.reach_succs`.
-/
import Kraken.Promising.Lin.Frame
import Kraken.Promising.LiveTermTreiber2P

namespace Kraken.Promising.Lin.T2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf Kraken.Promising.Live.Term Kraken.Promising.Live.TermTreiber2P
open Kraken.Promising.Live.TermTreiber2 (topL)
open Kraken.Promising.Live.TicketStep (spec_done spec_load)
open Kraken.Promising.Live.SemShape (spec_store_p)
open Kraken.Promising.Lin

variable [layout : _root_.Layout] (W : Program) (σ : Nat → Nat)

/-- The `treiber2` position of a state. -/
abbrev pos (s : isa.State) : Nat := posOf W σ true s.st.2

/-- **The layout**: `top` at `t`; thread `w < 2` owns node `nd w`, whose
only node word is its link `⟨n+8, 8⟩` (the payload is client data). -/
def t2L (t : BitVec 64) (nd : Nat → Node) : StackLayout where
  top := topL t
  link n := ⟨n + 8, 8⟩
  words n l := l = ⟨n + 8, 8⟩
  arena w n := w < 2 ∧ n = nd w
  link_word _ := rfl

/-- What a fragment step preserves: `X0` (`top`'s address) and `X1` (the
own node). -/
def keeps01 (s s' : isa.State) : Prop := s'.st.1.regs.X0 = s.st.1.regs.X0 ∧ s'.st.1.regs.X1 = s.st.1.regs.X1

/-- **The push fragment**: `X1` the node; returns at `10`. -/
def pushF : Frag isa where
  entry s := pos W σ s = 3
  inside s := 3 ≤ pos W σ s ∧ pos W σ s ≤ 8
  exit s := pos W σ s = 10
  arg s c := c = .push s.st.1.regs.X1.toBitVec
  res s op := op = .push s.st.1.regs.X1.toBitVec
  keeps := keeps01

/-- **The pop fragment**: returns at `17` (popped node in `X2`) or `21`
(empty, `X2 = 0`). -/
def popF : Frag isa where
  entry s := pos W σ s = 10
  inside s := 10 ≤ pos W σ s ∧ pos W σ s ≤ 16
  exit s := pos W σ s = 17 ∨ pos W σ s = 21
  arg _ c := c = .pop
  res s op := op.call = .pop ∧ s.st.1.regs.X2.toBitVec = (match op with | .pop (some n) => n | _ => 0)
  keeps := keeps01

/-- The two fragments (`true`: push). -/
def t2F : Bool → Frag isa
  | true => pushF W σ
  | false => popF W σ

/-- **Open**: the push fragment meets the framed spec. -/
def PushFragObl (t : BitVec 64) (nd : Nat → Node) : Prop := FragObl (t2L t nd) Arch.armv8 (pushF W σ)

/-- **Open**: the pop fragment meets the framed spec. -/
def PopFragObl (t : BitVec 64) (nd : Nat → Node) : Prop := FragObl (t2L t nd) Arch.armv8 (popF W σ)

/-- **The client invariant**: per thread, the static state, a position, its
node in `X1`, and before the push (position `1`) no committed own entry. -/
def t2CI (t : BitVec 64) (nd : Nat → Node) (c : Config isa) (H : List PEnt) : Prop :=
  ∀ w (u : Thread isa), c.threads[w]? = some u → w < 2 ∧ Static W σ true t u.st ∧ PcOK W σ true u.st ∧
    u.st.st.1.regs.X1.toBitVec = nd w ∧ (pos W σ u.st = 1 → ∀ e ∈ H, e.tid = w → e.pend = true)

theorem t2_disj : ∀ i k st, (t2F W σ i).inside st → (t2F W σ k).inside st → i = k := by
  intro i k st h1 h2
  cases i <;> cases k <;> simp only [t2F, pushF, popF] at h1 h2 <;> first | rfl | omega

omit layout in
/-- A history move of `v` keeps every entry of another thread. -/
theorem hmove_other {v : Nat} {last : Time} {H H' : List PEnt} (h : HMove v last H H') :
    ∀ e ∈ H', e.tid ≠ v → e ∈ H := by
  intro e he hv
  rcases h with rfl | ⟨q, op, b, -, rfl⟩ | ⟨H1, H2, q, op, rfl, rfl⟩ | ⟨r, rfl⟩
  · exact he
  · rcases List.mem_append.mp he with h | h
    · exact h
    · rw [List.mem_singleton] at h; subst h; exact absurd rfl hv
  · simp only [List.mem_append, List.mem_cons] at he ⊢
    rcases he with h | rfl | h
    · exact .inl h
    · exact absurd rfl hv
    · exact .inr (.inr h)
  · unfold insertRdP at he
    have : e ∈ H.takeWhile (fun e' => decide (e'.pos.ts ≤ r)) ++ H.dropWhile (fun e' => decide (e'.pos.ts ≤ r)) ∨
        e = ⟨.rd r, v, .pop none, false⟩ := by
      simp only [List.mem_append, List.mem_cons] at he ⊢
      rcases he with h | h | h
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
    rw [List.takeWhile_append_dropWhile] at this
    exact this.resolve_right fun h => hv (by rw [h])

omit layout in
/-- A 4-byte client message of `w` is a `ClientWriteOK` write. -/
theorem cw_d4 {t : BitVec 64} {nd : Nat → Node} {w : Nat} {q : Time} {n : BitVec 64} {v : Val} {H : List PEnt} :
    ClientWriteOK (t2L t nd) w q ⟨⟨n, 4⟩, v, w⟩ H :=
  ⟨rfl, fun h => by simp [t2L, topL] at h, fun n' h => by simp [t2L] at h⟩

omit layout in
/-- A client step changing neither memory nor promises respects the rely. -/
theorem commitOK_nop {L : StackLayout} {w : Nat} {c : Config isa} {u : Thread isa} {o : Outcome isa}
    {H : List PEnt} (hm : o.mem = c.mem) (hp : o.thread.prom = u.prom) :
    CommitOK L w c (c.withThread w o.thread o.mem) u o.thread H := by
  refine ⟨fun p h => hp ▸ h, fun p h _ _ _ => hp ▸ h, fun q m hg hq => ?_⟩
  change o.mem.get? q = some m at hg
  rw [hm] at hg
  rcases hq with hq | ⟨h1, h2⟩
  · exact absurd (get?_some_le hg).2 (Nat.not_le_of_lt hq)
  · exact absurd (hp ▸ h1) h2

omit layout in
/-- A client store (append or fulfilment, `WEff`) of a `ClientWriteOK`
message not to `top` respects the rely. -/
theorem commitOK_store {L : StackLayout} {w : Nat} {c : Config isa} {u : Thread isa} {o : Outcome isa}
    {H : List PEnt} {msg : Msg} (hS : Struct L c H) (hu : c.threads[w]? = some u)
    (hcw : ∀ q, ClientWriteOK L w q msg H) (h : WEff c.mem o.mem u.prom o.thread.prom msg) :
    CommitOK L w c (c.withThread w o.thread o.mem) u o.thread H := by
  have hnot : c.mem.last + 1 ∉ u.prom := fun h => absurd (hS.bnd w u hu _ h).2 (Nat.not_succ_le_self _)
  rcases h with ⟨hm, hp⟩ | ⟨ts, hts, hg0, hm, hp⟩
  · rw [List.erase_append_right _ hnot] at hp; simp only [List.erase_cons_head, List.append_nil] at hp
    refine ⟨fun p h => hp ▸ h, fun p h _ _ _ => hp ▸ h, fun q m hg hq => ?_⟩
    change o.mem.get? q = some m at hg
    rcases hq with hq | ⟨h1, h2⟩
    · have hq1 : q = c.mem.last + 1 := by
        have := (get?_some_le hg).2; rw [hm, Memory.last_append] at this
        exact Nat.le_antisymm this hq
      subst hq1; rw [hm, Memory.get?_append_last] at hg; cases hg; exact hcw _
    · exact absurd (hp ▸ h1) h2
  · refine ⟨fun p h => List.mem_of_mem_erase (hp ▸ h), fun p h m hg hl => ?_, fun q m hg hq => ?_⟩
    · have hne : p ≠ ts := fun e => by subst e; rw [hg0] at hg; cases hg; exact (hcw p).2.1 hl
      rw [hp]; exact (List.mem_erase_of_ne hne).mpr h
    · change o.mem.get? q = some m at hg
      rw [hm] at hg
      rcases hq with hq | ⟨h1, h2⟩
      · exact absurd (get?_some_le hg).2 (Nat.not_le_of_lt hq)
      · have : q = ts := Classical.byContradiction fun hne => h2 (by rw [hp]; exact (List.mem_erase_of_ne hne).mpr h1)
        subst this; rw [hg0] at hg; cases hg; exact hcw _

variable {W σ}

theorem pos_of_pc (C : Cells W σ true) {s : isa.State} {i : Nat} (hi : i ∈ pcsD true) (h : s.st.2 = pcS W σ i) :
    pos W σ s = i := by
  show posOf W σ true s.st.2 = i; rw [h, posOf_pcS C hi]

/-- **The client rely of `treiber2`, proved**: the client code (positions
`1`, `17`, `18`, `19`, `21`) writes only its 4-byte data word, keeps
`t2CI`, and enters `push` at its entry with its own unpushed node. -/
theorem t2_clientRely (C : Cells W σ true) {t : BitVec 64} {nd : Nat → Node} (hnd : ∀ w, nd w ≠ 0) :
    ClientRely (t2L t nd) Arch.armv8 (t2F W σ) (t2CI W σ t nd) where
  step := by
    intro w c c' a u hS _ hCI hu hout hI
    obtain ⟨u0, outs, o, hu0, hs, ho, -, rfl⟩ := hI
    rw [hu] at hu0; cases hu0
    obtain ⟨hw2, hSt, hPc, hX1, hp1⟩ := hCI w u hu
    have hstep := thread_step (N := 0) C hSt hs ho hPc
    obtain ⟨i, hi, hpc, -⟩ := hPc
    have hpos := pos_of_pc C hi hpc
    -- the common end: the new position `j`, `X1` kept, the rely
    have fin : ∀ j, pos W σ o.thread.st = j → ((j = 3 ∧ i = 1) ∨ j = 18 ∨ j = 19 ∨ j = 21) →
        o.thread.st.st.1.regs.X1 = u.st.st.1.regs.X1 →
        CommitOK (t2L t nd) w c (c.withThread w o.thread o.mem) u o.thread a.H →
        ∃ t', (c.withThread w o.thread o.mem).threads[w]? = some t' ∧
          CommitOK (t2L t nd) w c (c.withThread w o.thread o.mem) u t' a.H ∧
          t2CI W σ t nd (c.withThread w o.thread o.mem) a.H ∧
          ∀ k, (t2F W σ k).inside t'.st → Landing (t2L t nd) (t2F W σ k) w t' a.H := by
      intro j hj hjs hx hR
      refine ⟨o.thread, withThread_get_self hu, hR, fun v uv huv => ?_, fun k hk => ?_⟩
      · by_cases hv : v = w
        · subst hv; rw [withThread_get_self hu] at huv; cases huv
          exact ⟨hw2, hstep.st, hstep.pc, by rw [hx]; exact hX1, fun h1 => by omega⟩
        · rw [withThread_get_ne hu hv] at huv; exact hCI v uv huv
      · cases k <;> simp only [t2F, pushF, popF] at hk ⊢
        · omega
        · obtain ⟨rfl, rfl⟩ : j = 3 ∧ i = 1 := by omega
          exact ⟨hj, _, rfl, ⟨hw2, by rw [hx]; exact hX1⟩, by rw [hx, hX1]; exact hnd w,
            fun e he hew _ => hp1 hpos e he hew⟩
    have h1 := hout true; have h2 := hout false
    simp only [t2F, pushF, popF, hpos] at h1 h2
    have hi' : i = 1 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 21 := by
      simp only [pcsD, cPcs, ite_true, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hst, h⟩ := spec_store_p _ _ (C.str_d rfl _ (hSt.at C (by decide) (by decide) hpc) rfl (hSt.d4 rfl _))
        hs ho
      exact fin 3 (pos_of_pc C memC (by rw [hst])) (.inl ⟨rfl, rfl⟩) (by rw [hst] <;> rfl)
        (commitOK_store hS hu (fun _ => cw_d4) (WEff.of_store h))
    · obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (C.mov17 _ (hSt.at C memC (by decide) hpc)) hs ho
      exact fin 18 (pos_of_pc C (by decide) (by rw [hst] <;> rfl)) (.inr (.inl rfl)) (by rw [hst] <;> rfl)
        (commitOK_nop hm hp)
    · obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ :=
        spec_load _ _ (C.ldr18 rfl _ (hSt.at C (by decide) (by decide) hpc) rfl (hSt.d4 rfl _)) hs ho
      exact fin 19 (pos_of_pc C memC (by rw [hst])) (.inr (.inr (.inl rfl))) (by rw [hst] <;> rfl)
        (commitOK_nop hm hp)
    · obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (C.b19 _ (hSt.at C memC (by decide) hpc)) hs ho
      exact fin 21 (pos_of_pc C memC (by rw [hst])) (.inr (.inr (.inr rfl))) (by rw [hst] <;> rfl)
        (commitOK_nop hm hp)
    · rw [stepOne_end hSt hpc] at hs; cases hs
  frag := by
    intro k v c c' a a' t t' _ _ hCI ht hin hI ht' hLS hkeep _ hexit
    obtain ⟨u0, outs, o, hu0, hs, ho, -, rfl⟩ := hI
    rw [ht] at hu0; cases hu0
    rw [withThread_get_self ht] at ht'; cases ht'
    obtain ⟨hw2, hSt, hPc, hX1, -⟩ := hCI v t ht
    have hstep := thread_step (N := 0) C hSt hs ho hPc
    have hx : o.thread.st.st.1.regs.X1 = t.st.st.1.regs.X1 := by cases k <;> exact hkeep.2
    -- after a fragment step: inside, or at its exit
    have hp3 : 3 ≤ pos W σ o.thread.st := by
      by_cases h : (t2F W σ k).inside o.thread.st
      · cases k <;> simp only [t2F, pushF, popF] at h <;> omega
      · have := (hexit h).1; cases k <;> simp only [t2F, pushF, popF] at this <;> omega
    refine ⟨fun w uw huw => ?_, fun hn k' hk' => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [withThread_get_self ht] at huw; cases huw
        exact ⟨hw2, hstep.st, hstep.pc, by rw [hx]; exact hX1, fun h1 => by omega⟩
      · rw [withThread_get_ne ht hw] at huw
        obtain ⟨h1, h2, h3, h4, h5⟩ := hCI w uw huw
        exact ⟨h1, h2, h3, h4, fun hp e he hew =>
          h5 hp e (hmove_other (linStep_hmove hLS) e he (by rw [hew]; exact hw)) hew⟩
    · have hx := (hexit hn).1
      cases k <;> cases k' <;> simp only [t2F, pushF, popF] at hn hk' hx ⊢
      · exact absurd hk' hn
      · omega
      · exact ⟨hx, _, rfl, trivial⟩
      · exact absurd hk' hn
  prom := by
    intro v c c' a a' _ hP hPS hCI w u hu
    obtain ⟨t0, msg, ht0, -, htv, hthj, -⟩ := promSemInf_facts hP
    obtain ⟨-, m1, -, hH⟩ := hPS
    have hnew : ∀ e ∈ a'.H, e ∈ a.H ∨ e.pend = true := by
      intro e he; rw [hH] at he; unfold pAppend at he; split at he
      · rcases List.mem_append.mp he with h | h
        · exact .inl h
        · rw [List.mem_singleton] at h; subst h; exact .inr rfl
      · exact .inl he
    have hu0 : ∃ u0 : Thread isa, c.threads[w]? = some u0 ∧ u0.st = u.st := by
      by_cases hw : w = v
      · subst hw; rw [htv] at hu; cases hu; exact ⟨t0, ht0, rfl⟩
      · rw [hthj w hw] at hu; exact ⟨u, hu, rfl⟩
    obtain ⟨u0, hu0, hst⟩ := hu0
    obtain ⟨h1, h2, h3, h4, h5⟩ := hCI w u0 hu0
    rw [hst] at h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, fun hp e he hew => (hnew e he).elim (h5 hp e · hew) id⟩

/-- **`treiber2` from the framed pieces**: the lifting's obligations on the
fuel-free machine, with only the two fragment obligations open (the client
rely is `t2_clientRely`). -/
theorem t2_obl (C : Cells W σ true) {t : BitVec 64} {nd : Nat → Node} (hnd : ∀ w, nd w ≠ 0)
    (hPu : PushFragObl W σ t nd) (hPo : PopFragObl W σ t nd) :
    ∃ J, (linLift (t2L t nd) (t2F W σ) J (t2CI W σ t nd)).Obl Arch.armv8 :=
  linObl_of_fragObl (fun k => by cases k; exact hPo; exact hPu) (t2_disj W σ) (t2_clientRely C hnd)

/-- **`treiber2`, every step of the fuel-free semantic machine** carries the
composed invariant, with an abstract step (no liveness hypothesis), from the
two fragment obligations. -/
theorem t2_step (C : Cells W σ true) {t : BitVec 64} {nd : Nat → Node} (hnd : ∀ w, nd w ≠ 0)
    (hPu : PushFragObl W σ t nd) (hPo : PopFragObl W σ t nd) :
    ∃ J, ∀ {tid : Nat} {c c' : Config isa} {a : AS},
      (linLift (t2L t nd) (t2F W σ) J (t2CI W σ t nd)).Inv c a → StepSemInf Arch.armv8 tid c c' →
      ∃ a', (linLift (t2L t nd) (t2F W σ) J (t2CI W σ t nd)).Inv c' a' ∧
        (AStepL (t2L t nd) (t2F W σ) tid c c' a a' ∨ PStepL (t2L t nd) tid c c' a a') :=
  let ⟨J, h⟩ := t2_obl C hnd hPu hPo
  ⟨J, fun hinv hs => h.step hinv hs⟩

end Kraken.Promising.Lin.T2
