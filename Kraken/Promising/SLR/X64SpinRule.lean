/-
The x64 spinlock worker's rule (`X64SpinTrees.spinWorker`) in the
instance-anchored form `ThreadRuleRX` (`SLR/ThreadRuleX.lean`), from the
invariant `InvX` of `SLR/X64SpinInv.lean` and the cell rules of
`SLR/X64SpinCells.lean`. The x64 twin of `SLR/SwpRuleX.lean`.

`InvX` holds at the `NPSafe` instance `(c₀, g₀)`; at the extension `(c, g)`
the cells get `Inv` (`inv_env`) and `OwnPend` (`ownPend_transport`: an own
pending promise at `g` is pending at `g₀` already, hence a message of `c₀`,
hence not one of the promises the environment added). Away from positions 5,
10 and 11 (the three release writes, each of which may have been prepaid
under TSO) no own promise is pending (`noPend_of_ownPend`).

`done` is proved here; `wp` dispatches on the position: the cells that touch
no resource are `X64SpinCells`' rules, lifted by `HardCellsX.lift`; the
cells that touch resources and `prepay` are the fields of `HardCellsX`:

- `xchgl` (position 5), the counter store (10), the unlock (11): `CellWPX`,
  directly in the `EraseWPRD`/`InvX` form (each may fulfil an own pending
  promise; its other writes overtake it);
- the counter load (8): `CellWP`, lifted;
- `prepay`: `PrepayObX`, `ThreadRuleRX.prepay` for `InvX`;
- `lift`: `LiftOb`, the generic lift of a `WpPostR Inv` erasure WP from a
  state with no own pending promise to a `WpPostR InvX` one.

Position 14 (the end) has no step (`X64SpinTrees.exec_end`).
-/
import Kraken.Promising.SLR.X64SpinCells
import Kraken.Promising.SLR.X64SpinNoNT
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.SLR.RuleObligationsX

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-! ## The obligations -/

/-- `ThreadRuleR.wp` for the cell at position `i`, with `Inv` unfolded (as
`SwpInv.CellWP`); lifted to `InvX` by `HardCellsX.lift`. -/
def CellWP (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P.sys g → c.threads[tid]? = some t → Frame P t.st →
    LockWritesIn P.sys r c.mem → AtPos t.st i →
    Phase P tid cl i (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r →
    g₀.Le g → isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- `CellWP` for a state with no own pending promise. -/
def CellWPN (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P.sys g → c.threads[tid]? = some t → Frame P t.st →
    LockWritesIn P.sys r c.mem → AtPos t.st i →
    Phase P tid cl i (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r →
    g₀.Le g → isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∉ g.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- The cell obligation in `ThreadRuleRX` form: from `Inv`'s components and
`OwnPend` at the extension, the dead-branch erasure WP into `InvX`. -/
def CellWPX (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P.sys g → c.threads[tid]? = some t → Frame P t.st →
    LockWritesIn P.sys r c.mem → AtPos t.st i →
    Phase P tid cl i (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r → PrepaidProm P tid cl i t c.mem r →
    g₀.Le g → isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) → OwnPend P tid c r g →
    tree.EraseWPRD A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvX P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- `ThreadRuleRX.prepay` for `InvX`: the generic `PrepayObG`
(`SLR/RuleObligationsX.lean`). -/
def PrepayObX (P : Params) (A : Arch) (tid : Nat) : Prop :=
  PrepayObG A tid (InvX P tid)

/-- **The lift** of a cell proof from a state with no own pending promise:
after the instruction the pending marks are still messages (`g'.pend ⊆
g.pend`, the memory grows) and no own promise is pending (a fresh promise is
above every pending mark). The generic `LiftObG`. -/
def LiftOb (P : Params) (A : Arch) (tid : Nat) : Prop :=
  LiftObG A tid (Inv P tid) (InvX P tid)

/-- The open obligations of the worker's `ThreadRuleRX`: the four resource
cells, `prepay` and the lift. -/
structure HardCellsX (P : Params) (A : Arch) (tid : Nat) : Prop where
  xchg : CellWPX P A tid 5
  ldrC : CellWP P A tid 8
  strC : CellWPX P A tid 10
  unlock : CellWPX P A tid 11
  prepay : PrepayObX P A tid
  lift : LiftOb P A tid

/-! ## Environment and end -/

omit hv in
/-- **`Inv` under the environment**: an environment extension keeps the
thread's state and views, adds promises and grows the memory. -/
theorem inv_env {P : Params} {tid : Nat} {cl : Prop} {c c₁ : Config isa} {r : Res} {g g₁ : Ghost}
    (h : Inv P tid cl c r g) (he : EnvExt tid c c₁) (hle : g.Le g₁) : Inv P tid cl c₁ r g₁ := by
  obtain ⟨hW, t, ht, hF, hL, i, hp, hph, hpp⟩ := h
  obtain ⟨-, hpre, hth⟩ := he
  obtain ⟨ps, ht₁, -⟩ := hth t ht
  have hlast : c.mem.last ≤ c₁.mem.last := by
    have := hpre.length_le
    simp only [Array.length_toList] at this
    exact this
  refine ⟨hW.mono hle, _, ht₁, hF, fun p hp => Nat.le_trans (hL p hp) hlast, i, hp, hph,
    fun h10 hcl hq p hp hlt => ?_, fun h11 hq => ?_⟩
  · obtain ⟨w, hw, hwt⟩ := hpp.1 h10 hcl hq p hp hlt
    exact ⟨w, Memory.get?_of_prefix hpre hw, hwt⟩
  · obtain ⟨ts, hts, hw⟩ := hpp.2 h11 hq
    exact ⟨ts, List.mem_append_left _ hts, Memory.get?_of_prefix hpre hw⟩

/-- **`done`**: a halted worker is at the end, where `Phase` gives `Post`
under the clean flag. -/
theorem inv_done {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : Inv P tid cl c r g) (hcl : cl) (hd : c.Done tid) : Post P.N P.Lk P.K r := by
  obtain ⟨-, t, ht, hF, -, i, hp, hph, -⟩ := h
  obtain ⟨t', ht', hhalt, -⟩ := hd
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hnone : isa.exec t.st = none := by simpa [Thread.halted] using hhalt
  rcases Phase.pos hph with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_load_lock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hnone; cases hnone
  · rw [exec_test t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_jne_spin t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_mov_one t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_xchg t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hnone; cases hnone
  · rw [exec_test2 t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_jne_retry t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_load_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hnone; cases hnone
  · rw [exec_add t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_store_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hnone; cases hnone
  · rw [exec_unlock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hnone; cases hnone
  · rw [exec_jmp_done t.st (hF.at hp (by decide))] at hnone; cases hnone
  · exact hph.2 hcl

/-! ## Own pending promises -/

/-- Distinct instruction positions have distinct addresses (`n - 1` is an
instruction for `2 ≤ n ≤ 13`). -/
theorem addrOf_ne {k n : Nat} (hk : k < n) (hn : 2 ≤ n ∧ n ≤ 13) :
    (layout spinWorker).addrOf k ≠ (layout spinWorker).addrOf n := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact Executable.addrOf_ne_of_valid (layout spinWorker) hk
    (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [spinWorker]) (by
      intro l z
      rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [spinWorker])

/-- The positions of the release writes (5, 10, 11) have addresses of their
own among the positions of `Phase`. -/
theorem atPos_eq_rel {st : State} {i j : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 14)
    (hj : j = 5 ∨ j = 10 ∨ j = 11) (h : AtPos st i) (hj' : AtPos st j) : i = j := by
  have heq : (layout spinWorker).addrOf i = (layout spinWorker).addrOf j := h.symm.trans hj'
  have h14 : (layout spinWorker).addrOf 14 = (layout spinWorker).addrOf 13 :=
    addrOf_label (i := 13) (l := "done") rfl
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · exact absurd heq (addrOf_ne hlt (by omega))
  · rfl
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | omega
      | exact absurd heq.symm (addrOf_ne hgt (by omega))
      | (rw [h14] at heq; exact absurd heq.symm (addrOf_ne (by omega) (by omega)))

omit hv in
/-- **`OwnPend` at the extension**: an own pending promise at `g` is pending
at the instance ghost `g₀` (`NPSafe`'s transport), hence a message of `c₀`
(`PendIn`), hence one of the instance's promises, where `OwnPend` holds; the
environment's promises lie above `c₀`'s messages, and `c₀`'s messages are
messages of the extension. -/
theorem ownPend_transport {P : Params} {tid : Nat} {cl : Prop} {c₀ c : Config isa} {r : Res} {g₀ g : Ghost}
    (h : InvX P tid cl c₀ r g₀) (he : EnvExt tid c₀ c) {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) : OwnPend P tid c r g := by
  obtain ⟨⟨-, t₀, ht₀, -⟩, hPI, hOP⟩ := h
  obtain ⟨-, hpre, hth⟩ := he
  obtain ⟨ps, ht₁, hps⟩ := hth t₀ ht₀
  intro t' ht' ts hts hpd
  rw [ht] at ht'
  cases ht'
  rw [ht₁] at ht
  cases ht
  have h0 := hnp ts hts hpd
  rcases List.mem_append.mp hts with h | h
  · obtain ⟨hpos, hu, habove⟩ := hOP t₀ ht₀ ts h h0
    refine ⟨?_, fun ts' hts' hpd' => ?_, fun p hp hne w w' hw hw' hl => ?_⟩
    · rcases hpos with ⟨h5, hw⟩ | ⟨h10, hw⟩ | ⟨h11, hq, hw⟩
      · exact .inl ⟨h5, Memory.get?_of_prefix hpre hw⟩
      · exact .inr (.inl ⟨h10, Memory.get?_of_prefix hpre hw⟩)
      · exact .inr (.inr ⟨h11, hq, Memory.get?_of_prefix hpre hw⟩)
    · have h0' := hnp ts' hts' hpd'
      rcases List.mem_append.mp hts' with h' | h'
      · exact hu ts' h' h0'
      · exact absurd (hPI ts' h0') (Nat.not_le.mpr (hps ts' h'))
    · have hts0 : ts ≤ c₀.mem.last := hPI ts h0
      rcases List.mem_append.mp hp with h' | h'
      · by_cases hle : p ≤ c₀.mem.last
        · exact habove p h' hne w w' (Memory.get?_of_prefix_le hpre hle hw)
            (Memory.get?_of_prefix_le hpre hts0 hw') hl
        · exact Nat.lt_of_le_of_lt hts0 (Nat.not_le.mp hle)
      · exact Nat.lt_of_le_of_lt hts0 (hps p h')
  · exact absurd (hPI ts h0) (Nat.not_le.mpr (hps ts h))

/-- Away from positions 5, 10 and 11 no own promise is pending. -/
theorem noPend_of_ownPend {P : Params} {tid : Nat} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
    (hOP : OwnPend P tid c r g) (ht : c.threads[tid]? = some t) {i : Nat}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 14)
    (hp : AtPos t.st i) (hrel : i ≠ 5 ∧ i ≠ 10 ∧ i ≠ 11) : ∀ ts ∈ t.prom, ts ∉ g.pend := by
  intro ts hts hpd
  rcases (hOP t ht ts hts hpd).1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact hrel.1 (atPos_eq_rel hi (.inl rfl) hp h)
  · exact hrel.2.1 (atPos_eq_rel hi (.inr (.inl rfl)) hp h)
  · exact hrel.2.2 (atPos_eq_rel hi (.inr (.inr rfl)) hp h)

/-! ## The rule -/

/-- **The worker's rule** in `ThreadRuleRX` form, from `HardCellsX`. -/
def spinRuleX (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) :
    ThreadRuleRX (I := isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid where
  Inv := InvX P tid
  done := fun h he hle hcl hd => inv_done (inv_env h.1 he hle) hcl hd
  wp := fun {cl} {c₀} {c} {r} {g₀} {g} rF t tree h he hle ht hex E hinv hwf hnp => by
    have hOP := ownPend_transport h he ht hnp
    obtain ⟨hW, t', ht', hF, hL, i, hp, hph, hpp⟩ := inv_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    have hcl : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → cl := And.left
    have hpos := Phase.pos hph
    have hno := noPend_of_ownPend hOP ht hpos hp
    have hlift := @H.lift
    rcases hpos with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_load_lock hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_test hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_jne_spin hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_mov_one hW ht hF hL hp hph hex)
    · exact H.xchg g₀ rF t tree hW ht hF hL hp hph hpp hle hex E hinv hwf hnp hOP
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_test2 hcl hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_jne_retry hcl hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide))
        (H.ldrC g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_add hcl hW ht hF hL hp hph hex)
    · exact H.strC g₀ rF t tree hW ht hF hL hp hph hpp hle hex E hinv hwf hnp hOP
    · exact H.unlock g₀ rF t tree hW ht hF hL hp hph hpp hle hex E hinv hwf hnp hOP
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_jmp_done hcl hW ht hF hL hp hph hex)
    · rw [exec_end t.st hF.exe hp] at hex; cases hex
  prepay := fun rF t₁ w h he hle ht E hinv hnp hrel => H.prepay rF t₁ w h he hle ht E hinv hnp hrel

/-- **Every worker is non-promisingly safe**, from `HardCellsX`, at every
clean flag. -/
theorem spin_npsafeX (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) (n m : Nat) {cl : Prop}
    {c : Config isa} {r : Res} {g : Ghost} (h : InvX P tid cl c r g) :
    NPSafe (model isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid n m cl c r g :=
  NPSafe.of_ruleRX (spinRuleX P A tid H) n m cl c r g h

end Kraken.Promising.SLR.X64SpinInv
