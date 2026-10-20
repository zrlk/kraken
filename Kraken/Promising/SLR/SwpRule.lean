/-
The `ThreadRuleR` of the SWP spinlock worker (AArch64 `swpWorker`), from
the invariant `Inv` of `SLR/SwpInv.lean` and the cell rules of
`SLR/SwpCells.lean`.

`env` and `done` are proved here; `wp` dispatches on the position: the
silent cells and the spin load are `SwpCells`' rules; the cells that touch
resources (`swpa`, position 3; `ldr w5`, 10; `str w5`, 12; `stlr`, 13) and
`prepay` are the fields of `HardCells`, each stated exactly as `wp`
(resp. `prepay`) at that position.
-/
import Kraken.Promising.SLR.SwpPure
import Kraken.Promising.SLR.NPSafeInvR

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- `ThreadRuleR.wp` for the cell at position `i`, with `Inv` unfolded. -/
def CellWP (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), World P g → c.threads[tid]? = some t → Frame P t.st → LockWritesIn P r c.mem →
    AtPos t.st i → Phase P tid cl i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r →
    g₀.Le g → isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- `ThreadRuleR.prepay` for `Inv`. -/
def PrepayOb (P : Params) (A : Arch) (tid : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t₁ : Thread isa)
    (w : Msg), Inv P tid cl c r g → g₀.Le g → c.threads[tid]? = some t₁ → Erase (setRes rF tid r) g (fun _ => True) c →
    c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfils A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv P tid (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- The open obligations of the worker's rule: the four resource cells and
`prepay`. -/
structure HardCells (P : Params) (A : Arch) (tid : Nat) : Prop where
  swpa : CellWP P A tid 3
  ldrC : CellWP P A tid 10
  strC : CellWP P A tid 12
  stlr : CellWP P A tid 13
  prepay : PrepayOb P A tid

omit layout hv in
/-- `World` in a larger world. -/
theorem World.mono {P : Params} {g g₁ : Ghost} (h : World P g) (hle : g.Le g₁) : World P g₁ := by
  obtain ⟨hL, hC, ι, hι, hlt, hφ⟩ := h
  refine ⟨by rw [hle.rel]; exact hL, fun v => by rw [hle.rel]; exact hC v, ι, (hle.upd P.Lk).subset hι,
    Nat.lt_of_lt_of_le hlt (hle.acqTab.length_le), ?_⟩
  rw [← hφ]
  exact Ghost.acqPred_of_prefix hle.acqTab hlt

omit layout hv in
/-- The positions of `Phase`. -/
theorem Phase.pos {P : Params} {tid : Nat} {cl : Prop} {i : Nat} {x2 x5 : BitVec 32} {vs : Views} {r : Res}
    (h : Phase P tid cl i x2 x5 vs r) :
    i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨
      i = 16 := by
  revert h
  unfold Phase
  split <;> intro h <;> first | omega | exact h.elim

omit hv in
/-- **`env`**: an environment extension keeps the thread's state and views
and grows the memory. -/
theorem inv_env {P : Params} {tid : Nat} {cl : Prop} {c c₁ : Config isa} {r : Res} {g g₁ : Ghost}
    (h : Inv P tid cl c r g) (he : EnvExt tid c c₁) (hle : g.Le g₁) : Inv P tid cl c₁ r g₁ := by
  obtain ⟨hW, t, ht, hF, hL, i, hp, hph, hpp, hla⟩ := h
  have hpM : c.mem.Prefix c₁.mem := ⟨he.1, he.2.1⟩
  obtain ⟨-, hpre, hth⟩ := he
  obtain ⟨ps, ht₁, -⟩ := hth t ht
  have hlast : c.mem.last ≤ c₁.mem.last := by
    have := hpre.length_le
    simp only [Array.length_toList] at this
    exact this
  refine ⟨hW.mono hle, _, ht₁, hF, fun p hp => Nat.le_trans (hL p hp) hlast, i, hp, hph, fun h13 hq => ?_,
    fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  rotate_left
  · -- the environment only appends messages
    obtain ⟨w, hw, hw'⟩ := (hla f hf).1 h
    exact ⟨w, by rw [hpM.get? (Memory.last_le_of_get?_eq_some _ hw)]; exact hw, hw'⟩
  · cases hw : c₁.mem.writeIn P.Lk f.time (t.views.getCoh P.Lk)
    · have := (hla f hf).2 h; rw [hpM.writeIn hw] at this; cases this
    · rfl
  obtain ⟨ts, hts, hget⟩ := hpp h13 hq
  refine ⟨ts, List.mem_append_left _ hts, ?_⟩
  have hle := Memory.last_le_of_get?_eq_some _ hget
  obtain ⟨l, hl⟩ := hpre
  have h0 : ts ≠ 0 := fun h => by rw [h] at hget; simp [Memory.get?] at hget
  simp only [Memory.get?, h0, ↓reduceIte] at hget ⊢
  rw [← Array.getElem?_toList] at hget ⊢
  rw [← hl, List.getElem?_append_left (by simp only [Memory.last, Time] at hle h0; simp only [Array.length_toList]; omega)]
  exact hget

/-- **`done`**: a halted worker is at the end, where `Phase` gives `Post`
under the clean flag. -/
theorem inv_done {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : Inv P tid cl c r g) (hcl : cl) (hd : c.Done tid) : Post P.N P.Lk P.K r := by
  obtain ⟨-, t, ht, hF, -, i, hp, hph, -⟩ := h
  obtain ⟨t', ht', hhalt, -⟩ := hd
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hnone : isa.exec t.st = none := by simpa [Thread.halted] using hhalt
  rcases Phase.pos hph with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_swpa t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hnone; cases hnone
  · rw [exec_cbz t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_ldr_spin t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hnone; cases hnone
  · rw [exec_cbnz t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_b_try t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_ldr_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hnone; cases hnone
  · rw [exec_add t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_str_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hnone; cases hnone
  · rw [exec_stlr t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hnone; cases hnone
  · rw [exec_b_done t.st (hF.at hp (by decide))] at hnone; cases hnone
  · exact (hph.2 hcl)

/-- **The worker's rule**, from the open obligations `HardCells`. -/
def swpRule (P : Params) (A : Arch) (tid : Nat) (H : HardCells P A tid) :
    ThreadRuleR (I := isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid where
  Inv := Inv P tid
  env := inv_env
  done := fun h hcl hd => inv_done h hcl hd
  wp := fun {cl} {c} {r} {g} g₀ rF t tree h hle ht hex E hinv hwf hnp => by
    obtain ⟨hW, t', ht', hF, hL, i, hp, hph, -, hla⟩ := h
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    have hcl : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → cl := And.left
    rcases Phase.pos hph with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact wp_mov hW ht hF hL hp hph hla hex
    · exact H.swpa g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp
    · exact wp_cbz hcl hW ht hF hL hp hph hla hex
    · exact wp_ldr_spin hW ht hF hL hp hph hla hex
    · exact wp_cbnz hW ht hF hL hp hph hla hex
    · exact wp_b_try hW ht hF hL hp hph hla hex
    · exact H.ldrC g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp
    · exact wp_add hcl hW ht hF hL hp hph hex
    · exact H.strC g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp
    · exact H.stlr g₀ rF t tree hW ht hF hL hp hph hle hex E hinv hwf hnp
    · exact wp_b_done hcl hW ht hF hL hp hph hex
    · rw [exec_end hF hp] at hex; cases hex
  prepay := fun g₀ rF t₁ w h hle ht E hinv hnp hrel => H.prepay g₀ rF t₁ w h hle ht E hinv hnp hrel

/-- **Every worker is non-promisingly safe**, from `HardCells`, at every
clean flag. -/
theorem swp_npsafe (P : Params) (A : Arch) (tid : Nat) (H : HardCells P A tid) (n m : Nat) {cl : Prop}
    {c : Config isa} {r : Res} {g : Ghost} (h : Inv P tid cl c r g) :
    NPSafe (model isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid n m cl c r g :=
  NPSafe.of_ruleR (swpRule P A tid H) n m h

end Kraken.Promising.SLR.SwpInv
