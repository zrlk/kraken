/-
The SWP spinlock worker's rule in the instance-anchored form `ThreadRuleRX`
(`SLR/ThreadRuleX.lean`), whose invariant `InvX` (`SLR/SwpInv.lean`) may
speak about the thread's own pending promises.

`InvX` holds at the `NPSafe` instance `(c₀, g₀)`; at the extension `(c, g)`
the cells get `Inv` (`inv_env`) and `OwnPend` (`ownPend_transport`: an own
pending promise at `g` is pending at `g₀` already, hence a message of
`c₀`, hence not one of the promises the environment added). Before position
13 no own promise is pending (`noPend_of_ownPend`).

The obligations, `HardCellsX`:

- `swpa` (position 3): `CellWPN`, the `CellWP` form with no own pending
  promise;
- `ldrC`, `strC` (positions 10, 12): `CellWP` (`SLR/SwpStore.lean`);
- `stlr` (position 13): `CellWPX`, directly in the `EraseWPRD`/`InvX` form;
- `prepay`: `PrepayObX`, `ThreadRuleRX.prepay` for `InvX`;
- `lift`: `LiftOb`, the generic lift of a `WpPostR Inv` erasure WP from a
  state with no own pending promise to a `WpPostR InvX` one.
-/
import Kraken.Promising.SLR.SwpRule
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.SLR.RuleObligationsX

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-! ## The obligations -/

/-- `CellWP` for a state with no own pending promise. -/
def CellWPN (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P g → c.threads[tid]? = some t → Frame P t.st → LockWritesIn P r c.mem →
    AtPos t.st i → Phase P tid cl i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r →
    LkMem P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem →
    g₀.Le g → isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∉ g.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- The cell obligation in `ThreadRuleRX` form: from `Inv`'s components and
`OwnPend` at the extension, the dead-branch erasure WP into `InvX`. -/
def CellWPX (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P g → c.threads[tid]? = some t → Frame P t.st → LockWritesIn P r c.mem →
    AtPos t.st i → Phase P tid cl i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r → PrepaidProm P tid i t c.mem r →
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

/-- The open obligations of the worker's `ThreadRuleRX`. -/
structure HardCellsX (P : Params) (A : Arch) (tid : Nat) : Prop where
  swpa : CellWPN P A tid 3
  ldrC : CellWP P A tid 10
  strC : CellWP P A tid 12
  stlr : CellWPX P A tid 13
  prepay : PrepayObX P A tid
  lift : LiftOb P A tid

/-! ## Own pending promises -/

/-- Position 13 has an address of its own among the positions of `Phase`. -/
theorem atPos_eq_13 {st : State} {i : Nat}
    (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16)
    (h13 : AtPos st 13) (h : AtPos st i) : i = 13 := by
  have heq : (layout swpWorker).addrOf i = (layout swpWorker).addrOf 13 := h.symm.trans h13
  have hlt : ∀ k, k < 13 → (layout swpWorker).addrOf k ≠ (layout swpWorker).addrOf 13 := fun k hk =>
    Executable.addrOf_ne_of_valid (layout swpWorker) (k := k) (n := 13) hk
      (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker]) (by
        intro l z
        rw [Layout.apply_snd, Layout.frag_getElem?]
        simp [swpWorker])
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd heq (hlt 1 (by decide))
  · exact absurd heq (hlt 3 (by decide))
  · exact absurd heq (hlt 4 (by decide))
  · exact absurd heq (hlt 6 (by decide))
  · exact absurd heq (hlt 7 (by decide))
  · exact absurd heq (hlt 8 (by decide))
  · exact absurd heq (hlt 10 (by decide))
  · exact absurd heq (hlt 11 (by decide))
  · exact absurd heq (hlt 12 (by decide))
  · rfl
  · exact absurd heq.symm (Executable.addrOf_ne_of_valid (layout swpWorker) (k := 13) (n := 14) (by decide)
      (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker]) (by
        intro l z
        rw [Layout.apply_snd, Layout.frag_getElem?]
        simp [swpWorker]))
  · rw [addrOf_label (i := 15) (l := "done") rfl] at heq
    exact absurd heq.symm (Executable.addrOf_ne_of_valid (layout swpWorker) (k := 13) (n := 15) (by decide)
      (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker]) (by
        intro l z
        rw [Layout.apply_snd, Layout.frag_getElem?]
        simp [swpWorker]))

omit hv in
/-- **`OwnPend` at the extension**: an own pending promise at `g` is pending
at the instance ghost `g₀` (`NPSafe`'s transport), hence a message of `c₀`
(`PendIn`), hence one of the instance's promises, where `OwnPend` holds. -/
theorem ownPend_transport {P : Params} {tid : Nat} {cl : Prop} {c₀ c : Config isa} {r : Res} {g₀ g : Ghost}
    (h : InvX P tid cl c₀ r g₀) (he : EnvExt tid c₀ c) {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) : OwnPend P tid c r g := by
  obtain ⟨⟨-, t₀, ht₀, -⟩, hPI, hOP⟩ := h
  obtain ⟨-, -, hth⟩ := he
  obtain ⟨ps, ht₁, hps⟩ := hth t₀ ht₀
  intro t' ht' ts hts hpd
  rw [ht] at ht'
  cases ht'
  rw [ht₁] at ht
  cases ht
  have h0 := hnp ts hts hpd
  rcases List.mem_append.mp hts with h | h
  · obtain ⟨h13, hq, hu⟩ := hOP t₀ ht₀ ts h h0
    refine ⟨h13, hq, fun ts' hts' hpd' => ?_⟩
    have h0' := hnp ts' hts' hpd'
    rcases List.mem_append.mp hts' with h' | h'
    · exact hu ts' h' h0'
    · exact absurd (hPI ts' h0') (Nat.not_le.mpr (hps ts' h'))
  · exact absurd (hPI ts h0) (Nat.not_le.mpr (hps ts h))

/-- Away from position 13 no own promise is pending. -/
theorem noPend_of_ownPend {P : Params} {tid : Nat} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
    (hOP : OwnPend P tid c r g) (ht : c.threads[tid]? = some t) {i : Nat}
    (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16)
    (hp : AtPos t.st i) (h13 : i ≠ 13) : ∀ ts ∈ t.prom, ts ∉ g.pend :=
  fun ts hts hpd => h13 (atPos_eq_13 hi (hOP t ht ts hts hpd).1 hp)

/-! ## The rule -/

/-- **The worker's rule** in `ThreadRuleRX` form, from `HardCellsX`. -/
def swpRuleX (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) :
    ThreadRuleRX (I := isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid where
  Inv := InvX P tid
  done := fun h he hle hcl hd => inv_done (inv_env h.1 he hle) hcl hd
  wp := fun {cl} {c₀} {c} {r} {g₀} {g} rF t tree h he hle ht hex E hinv hwf hnp => by
    have hOP := ownPend_transport h he ht hnp
    obtain ⟨hW, t', ht', hF, hL, i, hp, hph, hpp, hla⟩ := inv_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    have hcl : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → cl := And.left
    have hpos := Phase.pos hph
    have hno := noPend_of_ownPend hOP ht hpos hp
    have hlift := @H.lift
    rcases hpos with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_mov hW ht hF hL hp hph hla hex)
    · exact hlift rF t tree ht E hinv (hno (by decide))
        (H.swpa g₀ rF t tree hW ht hF hL hp hph hla hle hex E hinv hwf (hno (by decide)))
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_cbz hcl hW ht hF hL hp hph hla hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_ldr_spin hW ht hF hL hp hph hla hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_cbnz hW ht hF hL hp hph hla hex)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_b_try hW ht hF hL hp hph hla hex)
    · exact hlift rF t tree ht E hinv (hno (by decide))
        (H.ldrC g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp)
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_add hcl hW ht hF hL hp hph hex)
    · exact hlift rF t tree ht E hinv (hno (by decide))
        (H.strC g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp)
    · exact H.stlr g₀ rF t tree hW ht hF hL hp hph hpp hle hex E hinv hwf hnp hOP
    · exact hlift rF t tree ht E hinv (hno (by decide)) (wp_b_done hcl hW ht hF hL hp hph hex)
    · rw [exec_end hF hp] at hex; cases hex
  prepay := fun rF t₁ w h he hle ht E hinv hnp hrel => H.prepay rF t₁ w h he hle ht E hinv hnp hrel

/-- **Every worker is non-promisingly safe**, from `HardCellsX`, at every
clean flag. -/
theorem swp_npsafeX (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) (n m : Nat) {cl : Prop}
    {c : Config isa} {r : Res} {g : Ghost} (h : InvX P tid cl c r g) :
    NPSafe (model isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid n m cl c r g :=
  NPSafe.of_ruleRX (swpRuleX P A tid H) n m cl c r g h

end Kraken.Promising.SLR.SwpInv
