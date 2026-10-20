/-
EnvG, live trees (x64 part): **every x64 instruction tree is live**.

The x64 adapter `Promising.X64.toEv` emits every `rmw` (and `rmw16`) with
`noRet := false` (x86 has no `NoRet` atomics), so no static check is needed:
`toEv_rmwLive` holds for every effect tree and every declaration table, and
`exec_rmwLive` for every thread state. A live tree judgment
(`EnvG.TreeJLive`) therefore applies to x64 trees through
`TreeJLive.toTreeJ` with no hypothesis on the program.

Phase 1: single-access trees; the lemmas here hold
for every tree.
-/
import Kraken.Promising.X64
import Kraken.Promising.SLR.EnvG.Live

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising

theorem access_live {σ : Type} {ds : Decls} {addr : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (hk : ∀ l, (k l).RmwLive) : (EvTree.access ds addr n k).RmwLive := by
  unfold EvTree.access
  split
  · exact hk _
  · trivial

theorem loadPieces_live {σ : Type} {ds : Decls} {dmem : DataMem} :
    ∀ (n : Nat) {addr : BitVec 64} {k : List UInt8 → EvTree σ}, (∀ bs, (k bs).RmwLive) →
      (loadPieces ds dmem addr n k).RmwLive
  | 0, _, _, hk => hk _
  | n + 1, addr, k, hk => by
    unfold loadPieces
    simp only
    split
    · exact loadPieces_live n fun _ => hk _
    · split
      · trivial
      · exact access_live fun _ _ => loadPieces_live n fun _ => hk _

theorem storePieces_live {σ : Type} {ds : Decls} :
    ∀ (n : Nat) {addr : BitVec 64} {bs : List UInt8} {dmem : DataMem} {k : DataMem → EvTree σ},
      (∀ d, (k d).RmwLive) → (storePieces ds addr n bs dmem k).RmwLive
  | 0, _, _, _, _, hk => hk _
  | n + 1, addr, bs, dmem, k, hk => by
    unfold storePieces
    split
    · exact storePieces_live n hk
    · split
      · trivial
      · exact access_live fun _ _ => storePieces_live n hk

/-- **x64 trees are live**: the adapter's `rmw` nodes all have
`noRet = false` (`X64.lean`, `toEv`'s `rmw` and `rmw16` cases). -/
theorem toEv_rmwLive (ds : Decls) (e : Effects) : (toEv ds e).RmwLive := by
  induction e with
  | done => trivial
  | unimplemented => trivial
  | gp_unaligned => trivial
  | nonmem_load _ _ _ _ ih => exact access_live fun _ _ => ih _ _
  | nonmem_store _ _ _ _ ih => exact access_live fun _ _ => ih _
  | undefined ret ih =>
    rename_i α inst
    cases inst with
    | bool => exact fun _ => ih _
    | bitvec => trivial
    | avx_bitvec => trivial
    | statusFlags => trivial
  | require_read_access _ _ _ ih => exact ih _
  | require_write_access _ _ _ ih => exact ih _
  | require_exec_access _ _ ih => exact ih _
  | sync_load _ _ _ _ _ _ ih => exact access_live fun _ _ => ih _ _
  | sync_store _ _ _ _ _ _ ih => exact access_live fun _ _ => ih _ _
  | rmw _ _ _ _ _ _ ih => exact access_live fun _ => ⟨rfl, fun _ => ih _ _⟩
  | fence _ _ ih => exact fun _ => ih _
  | require_read_access_avx _ _ _ _ ih => exact ih _
  | require_write_access_avx _ _ _ _ ih => exact ih _
  | nonmem_load_avx _ _ _ _ _ ih =>
    simp only [toEv]
    split
    · exact access_live fun _ _ => ih _ _
    · exact loadPieces_live _ fun _ => ih _ _
  | nonmem_store_avx _ _ _ _ _ ih =>
    simp only [toEv]
    split
    · exact access_live fun _ _ => ih _
    · exact storePieces_live _ fun _ => ih _
  | rmw16 _ _ _ _ _ ih => exact access_live fun _ => ⟨rfl, fun _ => ih _ _⟩

/-- **Every x64 instruction tree is live** (no static check needed). -/
theorem exec_rmwLive (st : State) : ∀ tree, isa.exec st = some tree → tree.RmwLive := by
  intro tree htree
  simp only [isa, exec] at htree
  split at htree
  · cases htree
  · cases htree
    exact (EvTree.rmwLive_map (σ := MachineState) (τ := State) _ _).mpr (toEv_rmwLive _ _)

end Kraken.Promising.X64.EnvG
