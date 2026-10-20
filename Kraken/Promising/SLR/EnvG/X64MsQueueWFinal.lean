/-
**The final law of the x64 MS queue for try-once dequeuers** (one enqueuer
of `n1` then `n2`; `EnvG/X64MsQueueWGhost.lean`). ISA-neutral.

At a final configuration with a clean erasure at the ghost facts `GWW`, in
which the acquire id `0` of every queue word is held:

- every non-initial message of a queue word has an id-`0` slot in `formW`
  (`msg_formW`);
- **the history** (`histW`, strong induction on the timestamp) is
  `X64MsQueue2Final.Hist` without `HH` (`head` may be ahead of `tail`): the
  values of `head`/`tail` are `HT` values, the non-initial link messages are
  `LK`. At a swing of `head` (`head_stepW`) the overwritten `z` is an `HT`
  value and the link read of `[z]` is non-zero, so `link_succW` makes the
  value written an `HT` value of rank `rk z + 1` (`[n2]` has no non-zero
  message);
- **the `head` chain** (`head_msgW`, `head_pairW`): a non-initial message of
  `head` is `n1` over an adjacent `s`, or `n2` over an adjacent `n1`; of two
  of them the earlier is `n1` and the later `n2`;
- **`tokQ`** (`deq_n2W`): a `head` message of `n2` overwrote a `head`
  message of `n1` whose slot holds `tokQ` whole (`TokN1`, its second
  disjunct excluded by `head_pairW`);
- **one dequeuer calling twice** (`DoneW`: per call its own `head` message
  or empty, and `tokQ` still held unless a call returned `n1`): the results
  are `(n1, n2)`, `(n1, ∅)`, `(∅, n1)` or `(∅, ∅)` (`final_valuesW`).
-/
import Kraken.Promising.SLR.EnvG.X64MsQueueWGhost

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read?)
open Kraken.Promising.X64.EnvG.Treiber2X (get?_ne_zero)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The history at `V` (`Hist` without `HH`). -/
def HistW (P : Params) (m : Memory) (V : Time) : Prop :=
  (∀ x y, (x = P.head ∨ x = P.tail) → m.read? x V = some y → HT P m V (BitVec.setWidth 64 y)) ∧
    (∀ x v w, P.IsL x → m.get? V = some ⟨x, v, w⟩ → LK P m V x (BitVec.setWidth 64 v))

/-- **One dequeuer calling twice, done**, holding `R`: per call its own
`head` message (`some`, the two in order) or empty (`none`), and `tokQ`
whole unless a call returned `n1`. -/
def DoneW (m : Memory) (P : Params) (R : Res) (r1 r2 : Option (BitVec 64)) : Prop :=
  (TokFrozen P.tokQ R ∨ r1 = some P.n1 ∨ r2 = some P.n1) ∧
    match r1, r2 with
    | some x, some y => DoneD2 m P x y
    | some x, none => ∃ V, Deq m P V x
    | none, some y => ∃ V, Deq m P V y
    | none, none => True

/-- `DoneW` survives a memory extension. -/
theorem DoneW.mono {P : Params} {m m' : Memory} (h : m.Prefix m') {R : Res} {r1 r2 : Option (BitVec 64)}
    (hd : DoneW m P R r1 r2) : DoneW m' P R r1 r2 := by
  obtain ⟨ht, hd⟩ := hd; refine ⟨ht, ?_⟩
  rcases r1 with _ | x <;> rcases r2 with _ | y
  · trivial
  · exact (hd : ∃ V, Deq m P V y).imp fun _ hv => hv.mono h
  · exact (hd : ∃ V, Deq m P V x).imp fun _ hv => hv.mono h
  · exact (hd : DoneD2 m P x y).mono h

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **Every non-initial message of a queue word has an id-`0` slot in
`formW`.** -/
theorem msg_formW (E : Erase rF g TT c) (hW : GWW P g) {x : Loc} (hx : P.IsW x)
    (htot : (total rF g c).acq x 0 = 1) {V : Time} {v : Val} {w : Nat} (hV : c.mem.get? V = some ⟨x, v, w⟩) :
    ∃ s ∈ g.u, s.key = (x, V) ∧ (P.IsL x → LinkF P c.mem V s.res x v) ∧
      (x = P.head → HeadFW P c.mem V v ∨ TailLoc P c.mem V x) ∧
      (x = P.tail → TailF P c.mem V v ∨ TailLoc P c.mem V x) ∧
      (x = P.head → TailLoc P c.mem V x ∨ TokN1 P c.mem V s.res v) := by
  have hrd : c.mem.read? (x, V).1 (x, V).2 = some v := read?_of_get? hV
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E htot hrd (hW.impure hx v)
  rw [hW.acqPred_zero] at hP
  obtain ⟨x', w', hg, h1, h2, h3, -, h5⟩ := hP (get?_ne_zero hV)
  rw [hV] at hg
  cases hg
  exact ⟨s, hs, hk, h1, h2, h3, h5⟩

variable (E : Erase rF g TT c) (hW : GWW P g) (hL : QLocs P) (hi : InitV c.mem P)
  (htot : ∀ x, P.IsW x → (total rF g c).acq x 0 = 1)
include E hW hL hi htot

omit hi in
/-- Two link messages of the same node (`n1` or `n2`) at different times
contradict validity (their slots hold the node's token whole). -/
theorem two_linkW {n : BitVec 64} (hn : n = P.n1 ∨ n = P.n2) {x x' : Loc} (hx : P.IsL x) (hx' : P.IsL x')
    {V V' : Time} {v v' : Val} {w w' : Nat} (hg : c.mem.get? V = some ⟨x, v, w⟩)
    (hg' : c.mem.get? V' = some ⟨x', v', w'⟩) (hv : BitVec.setWidth 64 v = n) (hv' : BitVec.setWidth 64 v' = n)
    (hne : V ≠ V') : False := by
  have key : ∀ {x V v w}, P.IsL x → c.mem.get? V = some ⟨x, v, w⟩ → BitVec.setWidth 64 v = n →
      ∃ s ∈ g.u, s.key = (x, V) ∧ TokFrozen (if n = P.n1 then P.tok1 else P.tok2) s.res := by
    intro x V v w hx hg hv
    obtain ⟨s, hs, hk, h1, -⟩ := msg_formW E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
    refine ⟨s, hs, hk, ?_⟩
    rcases (h1 hx).1 with ⟨hv1, hf⟩ | ⟨hv2, hf, -⟩ <;> rcases hn with rfl | rfl
    · simpa using hf
    · exact absurd (hv1.symm.trans hv) hL.n12
    · exact absurd (hv.symm.trans hv2) hL.n12
    · simpa [Ne.symm hL.n12] using hf
  obtain ⟨s, hs, hk, hf⟩ := key hx hg hv
  obtain ⟨s', hs', hk', hf'⟩ := key hx' hg' hv'
  exact tok_unique E hs hs' (by rw [hk, hk']; intro h; exact hne (congrArg Prod.snd h).symm) hf hf'

section Step

variable {V : Time} (ih : ∀ V' < V, HistW P c.mem V')
include ih

omit E hW hL htot in
theorem link_readW {x : Loc} (hx : P.IsL x) {b : Time} (hb : b < V) {y : Val} (hr : c.mem.read? x b = some y)
    (hy : BitVec.setWidth 64 y ≠ 0) : ∃ w, c.mem.get? b = some ⟨x, y, w⟩ ∧ LK P c.mem b x (BitVec.setWidth 64 y) := by
  obtain ⟨w, hg⟩ := msg_of_read (ne_zero_of_link hi hx hr hy) hr
  exact ⟨w, hg, (ih b hb).2 x y w hx hg⟩

omit E hW hL hi htot in
theorem isL_of_tailLocW {V' : Time} (hV : V' ≤ V) {x : Loc} (ht : TailLoc P c.mem V' x) : P.IsL x := by
  obtain ⟨a, y, ha, hr, rfl⟩ := ht
  exact isL_of_HT ((ih a (by omega_t)).1 _ _ (.inr rfl) hr)

omit E hW hL hi htot in
theorem linkMsg_LKW {V0 : Time} (hV : V0 ≤ V) {n : BitVec 64} (hl : LinkMsg P c.mem V0 n) :
    ∃ b < V0, ∃ x v w, c.mem.get? b = some ⟨x, v, w⟩ ∧ BitVec.setWidth 64 v = n ∧ LK P c.mem b x n := by
  obtain ⟨b, x, v, w, hb, hg, hv, ht⟩ := hl
  exact ⟨b, hb, x, v, w, hg, hv, hv ▸ (ih b (by omega_t)).2 x v w (isL_of_tailLocW ih hV ht) hg⟩

omit E hW htot in
/-- **One link past** (`link_succ` at `HistW`). -/
theorem link_succW {V0 : Time} {z : BitVec 64} (hz : HT P c.mem V0 z) {b : Time} (hb : b < V) {y5 : Val}
    (hr : c.mem.read? ⟨z, 8⟩ b = some y5) (hy : BitVec.setWidth 64 y5 ≠ 0) :
    HT P c.mem V (BitVec.setWidth 64 y5) ∧ rk P (BitVec.setWidth 64 y5) = rk P z + 1 := by
  obtain ⟨w, hg, hk⟩ := link_readW hi ih (isL_of_HT hz) hb hr hy
  refine ⟨HT_of_LK hg hk hb, ?_⟩
  rcases hk with ⟨h, hv⟩ | ⟨h, hv, -⟩
  · simp only [Params.ls, Loc.mk.injEq, and_true] at h
    rw [hv, h, rk_n1 hL, rk_s hL]
  · simp only [Params.l1, Loc.mk.injEq, and_true] at h
    rw [hv, h, rk_n2, rk_n1 hL]

omit E hW hi htot in
theorem not_tailLocW {V' : Time} (hV : V' ≤ V) {x : Loc} (hx : x = P.head ∨ x = P.tail) :
    ¬ TailLoc P c.mem V' x := fun ht => by
  rcases hx with rfl | rfl
  · exact hL.not_isL_head (isL_of_tailLocW ih hV ht)
  · exact hL.not_isL_tail (isL_of_tailLocW ih hV ht)

omit E hW htot in
/-- **The dequeuer's swing**: the value written is an `HT` value one rank
past the overwritten `z`. -/
theorem head_stepW {v : Val} (hh : HeadFW P c.mem V v) :
    ∃ tr z, tr < V ∧ c.mem.read? P.head tr = some z ∧ NoMsgIn c.mem P.head tr V ∧
      HT P c.mem V (BitVec.setWidth 64 v) ∧ rk P (BitVec.setWidth 64 v) = rk P (BitVec.setWidth 64 z) + 1 := by
  obtain ⟨hnz, tr, z, b, y, htr, hrz, hnm, hb, hry, hyv⟩ := hh
  have := link_succW hL hi ih ((ih tr htr).1 _ _ (.inl rfl) hrz) hb hry (by rw [hyv]; exact hnz)
  rw [hyv] at this
  exact ⟨tr, z, htr, hrz, hnm, this⟩

/-- **The history step.** -/
theorem hist_stepW : HistW P c.mem V := by
  have hlow : ∀ a < V, ∀ x y, (x = P.head ∨ x = P.tail) → c.mem.read? x a = some y →
      HT P c.mem V (BitVec.setWidth 64 y) := by
    intro a ha x y hx hr
    rcases (ih a ha).1 x y hx hr with h | ⟨h, b, hb, hb'⟩ | ⟨h, b, hb, hb'⟩
    · exact .inl h
    · exact .inr (.inl ⟨h, b, by omega_t, hb'⟩)
    · exact .inr (.inr ⟨h, b, by omega_t, hb'⟩)
  refine ⟨fun x y hx hr => ?_, fun x v w hx hg => ?_⟩
  · by_cases hV : V = 0
    · subst hV
      simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rcases hx with rfl | rfl
      · exact .inl hi.head
      · exact .inl hi.tail
    obtain ⟨w, hg⟩ := msg_of_read hV hr
    have hxw : P.IsW x := by rcases hx with rfl | rfl <;> simp [Params.IsW]
    obtain ⟨s, -, -, -, h2, h3, -⟩ := msg_formW E hW hxw (htot x hxw) hg
    rcases hx with rfl | rfl
    · rcases h2 rfl with hh | ht
      · obtain ⟨-, -, -, -, -, h, -⟩ := head_stepW hL hi ih hh
        exact h
      · exact absurd ht (not_tailLocW hL ih (Nat.le_refl _) (.inl rfl))
    · rcases h3 rfl with ⟨hnz, tr, z, b, y5, htr, hrz, -, hb, hr5, hyy⟩ | ht
      · rw [← hyy] at hnz ⊢
        exact (link_succW hL hi ih ((ih tr htr).1 _ _ (.inr rfl) hrz) hb hr5 hnz).1
      · exact absurd ht (not_tailLocW hL ih (Nat.le_refl _) (.inr rfl))
  · obtain ⟨s, hs, hk, h1, -⟩ := msg_formW E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
    obtain ⟨hnode, ⟨a, y3, ha, hr3, rfl⟩, tr, z, htr, hrz, hz0, hnm⟩ := h1 hx
    rcases hlow a ha _ _ (.inr rfl) hr3 with hy | ⟨hy, b, hb, v1, w1, hg1, hv1⟩ |
        ⟨hy, b, hb, v2, w2, hg2, hv2, b1, hb1, v1, w1, hg1, hv1⟩
    · rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact .inl ⟨by rw [hy]; rfl, hv⟩
      · exfalso
        obtain ⟨b, hb, x', v', w', hg', hv', hk⟩ := linkMsg_LKW ih (Nat.le_refl _) hl
        have hx' : x' = P.ls := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        have hloc : (⟨BitVec.setWidth 64 y3, 8⟩ : Loc) = P.ls := by rw [hy]; rfl
        rw [hloc] at hrz hnm
        by_cases htb : tr < b
        · exact hnm b _ htb hb hg' rfl
        have htr0 : tr ≠ 0 := by have := get?_ne_zero hg'; omega_t
        obtain ⟨wz, hgz⟩ := msg_of_read htr0 hrz
        rcases (ih tr htr).2 _ z wz (.inl rfl) hgz with ⟨-, h⟩ | ⟨-, h, -⟩
        · exact hL.n1z (h.symm.trans hz0)
        · exact hL.n2z (h.symm.trans hz0)
    · have hloc : (⟨BitVec.setWidth 64 y3, 8⟩ : Loc) = P.l1 := by rw [hy]; rfl
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact (two_linkW E hW hL htot (.inl rfl) (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · obtain ⟨b', hb', x', v', w', hg', hv', hk⟩ := linkMsg_LKW ih (Nat.le_refl _) hl
        have hx' : x' = P.ls := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        exact .inr ⟨hloc, hv, b', hb', v', w', hg', hv'⟩
    · rcases hnode with ⟨hv, -⟩ | ⟨hv, -, -⟩
      · exact (two_linkW E hW hL htot (.inl rfl) (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · exact (two_linkW E hW hL htot (.inr rfl) (.inr (.inl rfl)) hx hg2 hg hv2 hv (by omega_t)).elim

end Step

/-- **The history**, at every time. -/
theorem histW : ∀ V, HistW P c.mem V := by
  intro V
  induction V using Nat.strongRecOn with
  | _ V ih => exact hist_stepW E hW hL hi htot ih

/-- **A non-initial message of `head`** overwrote an adjacent `s` and is
`n1`, or overwrote an adjacent `n1` and is `n2`. -/
theorem head_msgW {V : Time} {y : Val} {w : Nat} (hg : c.mem.get? V = some ⟨P.head, y, w⟩) :
    ∃ tr z, tr < V ∧ c.mem.read? P.head tr = some z ∧ NoMsgIn c.mem P.head tr V ∧
      ((BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 z = P.s) ∨
        (BitVec.setWidth 64 y = P.n2 ∧ BitVec.setWidth 64 z = P.n1)) := by
  obtain ⟨s, -, -, -, h2, -⟩ := msg_formW E hW (.inl rfl) (htot _ (.inl rfl)) hg
  have H := histW E hW hL hi htot
  rcases h2 rfl with hh | ht
  · obtain ⟨tr, z, htr, hrz, hnm, hHy, hrk⟩ := head_stepW hL hi (fun V' _ => H V') hh
    have hHz := (H tr).1 _ _ (.inl rfl) hrz
    refine ⟨tr, z, htr, hrz, hnm, ?_⟩
    rcases rk_cases hL hHy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases rk_cases hL hHz with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first | omega | exact .inl ⟨h1, h3⟩ | exact .inr ⟨h1, h3⟩
  · exact absurd ht (not_tailLocW hL (fun V' _ => H V') (Nat.le_refl _) (.inl rfl))

/-- **Two non-initial messages of `head`**: the earlier is `n1`, the later
`n2`. -/
theorem head_pairW {V V' : Time} (hVV : V < V') {y y' : Val} {w w' : Nat}
    (hg : c.mem.get? V = some ⟨P.head, y, w⟩) (hg' : c.mem.get? V' = some ⟨P.head, y', w'⟩) :
    BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 y' = P.n2 := by
  have hnd : ∀ t z, V ≤ t → c.mem.read? P.head t = some z → BitVec.setWidth 64 z ≠ P.s := by
    intro t z ht hr hz
    obtain ⟨wt, hgt⟩ := msg_of_read (by have := get?_ne_zero hg; omega_t) hr
    obtain ⟨_, _, _, _, _, h⟩ := head_msgW E hW hL hi htot hgt
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hL.s1 (hz.symm.trans h)
    · exact hL.s2 (hz.symm.trans h)
  obtain ⟨tr, z, htr, hrz, hnm, h⟩ := head_msgW E hW hL hi htot hg'
  have hVtr : V ≤ tr := Classical.byContradiction fun hc => hnm V _ (by omega_t) hVV hg rfl
  rcases h with ⟨-, hz⟩ | ⟨hy', hz⟩
  · exact absurd hz (hnd tr z hVtr hrz)
  refine ⟨?_, hy'⟩
  rcases Nat.eq_or_lt_of_le hVtr with heq | hlt
  · subst heq
    rw [read?_of_get? hg] at hrz
    cases hrz; exact hz
  · obtain ⟨wt, hgt⟩ := msg_of_read (by omega_t) hrz
    obtain ⟨tr', z', htr', hrz', hnm', h'⟩ := head_msgW E hW hL hi htot hgt
    have hVtr' : V ≤ tr' := Classical.byContradiction fun hc => hnm' V _ (by omega_t) hlt hg rfl
    rcases h' with ⟨-, hz'⟩ | ⟨h', -⟩
    · exact absurd hz' (hnd tr' z' hVtr' hrz')
    · exact absurd (hz.symm.trans h') hL.n12

/-- **A dequeue of `n2`** overwrote a `head` message of `n1` whose slot holds
`tokQ` whole. -/
theorem deq_n2W (hpt : P.trk = false) {V : Time} (hd : Deq c.mem P V P.n2) :
    ∃ V' < V, ∃ s ∈ g.u, s.key = (P.head, V') ∧ TokFrozen P.tokQ s.res := by
  obtain ⟨vh, w, hg, hv⟩ := hd
  obtain ⟨tr, z, htr, hrz, -, h⟩ := head_msgW E hW hL hi htot hg
  have hz : BitVec.setWidth 64 z = P.n1 := by
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (hv.symm.trans h1) (Ne.symm hL.n12)
    · exact h2
  have htr0 : tr ≠ 0 := by
    rintro rfl
    simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hrz
    subst hrz
    exact hL.s1 (hi.head.symm.trans hz)
  obtain ⟨w', hg'⟩ := msg_of_read htr0 hrz
  obtain ⟨s, hs, hk, -, -, -, h5⟩ := msg_formW E hW (.inl rfl) (htot _ (.inl rfl)) hg'
  have H := histW E hW hL hi htot
  rcases h5 rfl with ht | ht
  · exact absurd ht (not_tailLocW hL (fun V' _ => H V') (Nat.le_refl _) (.inl rfl))
  rcases ht hpt hz with ht | ⟨V'', hV'', vh'', w'', hg'', hv''⟩
  · exact ⟨tr, htr, s, hs, hk, ht⟩
  · exact (hL.n12 (hz.symm.trans (head_pairW E hW hL hi htot hV'' hg'' hg').2)).elim

/-- **A dequeue by the thread `k` still holding `tokQ`, or of `n1`**, is a
dequeue of `n1`. -/
theorem deq_oneW (hpt : P.trk = false) {k : Nat} (hk : k < c.threads.size) {x : BitVec 64}
    (htk : TokFrozen P.tokQ (rF k) ∨ x = P.n1) {V : Time} (hd : Deq c.mem P V x) : x = P.n1 := by
  rcases htk with htk | h
  · obtain ⟨vh, w, hg, rfl⟩ := id hd
    obtain ⟨_, _, _, _, _, h⟩ := head_msgW E hW hL hi htot hg
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [h] at hd
      obtain ⟨V', -, s, hs, -, hts⟩ := deq_n2W E hW hL hi htot hpt hd
      have := E.q_add_le_one_slot hk hs P.tokQ
      unfold TokFrozen at htk hts
      grind
  · exact h

/-- **One dequeuer (thread `k`) calling twice**: the results are `(n1, n2)`,
`(n1, ∅)`, `(∅, n1)` or `(∅, ∅)`. -/
theorem final_valuesW (hpt : P.trk = false) {k : Nat} (hk : k < c.threads.size) {r1 r2 : Option (BitVec 64)}
    (hd : DoneW c.mem P (rF k) r1 r2) :
    (r1 = some P.n1 ∧ r2 = some P.n2) ∨ (r1 = some P.n1 ∧ r2 = none) ∨ (r1 = none ∧ r2 = some P.n1) ∨
      (r1 = none ∧ r2 = none) := by
  obtain ⟨htk, hd⟩ := hd
  rcases r1 with _ | x <;> rcases r2 with _ | y
  · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
  · obtain ⟨V, hV⟩ := hd
    refine .inr (.inr (.inl ⟨rfl, ?_⟩))
    rw [deq_oneW E hW hL hi htot hpt hk (htk.imp id fun h => h.elim (fun h => by cases h) Option.some.inj) hV]
  · obtain ⟨V, hV⟩ := hd
    refine .inr (.inl ⟨?_, rfl⟩)
    rw [deq_oneW E hW hL hi htot hpt hk (htk.imp id fun h => h.elim Option.some.inj fun h => by cases h) hV]
  · change DoneD2 c.mem P x y at hd
    obtain ⟨V1, V2, h12, ⟨vh1, w1, hg1, hx⟩, ⟨vh2, w2, hg2, hy⟩⟩ := hd
    obtain ⟨h1, h2⟩ := head_pairW E hW hL hi htot h12 hg1 hg2
    exact .inl ⟨by rw [← hx, h1], by rw [← hy, h2]⟩

end Final

end Kraken.Promising.X64.EnvG.MsQueueX
