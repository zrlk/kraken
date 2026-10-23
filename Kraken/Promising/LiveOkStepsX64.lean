/-
**x64: every x64 instruction tree is total.**

The `ISA.ExecTotal` instance for `X64.isa`: every tree the adapter `toEv`
builds has an outcome from every bounded, promise-free context
(`EvTree.Total`, `LiveOkSteps.lean`). The adapter has no `choose 0` (its only
choice is `undefined Bool`), so every node is covered by the generic closure
lemmas; the vector pieces (`loadPieces`/`storePieces`) by induction on the
number of pieces.

With this instance `Live.NoStuck.stuckHasDeadPromise_of_faultFreeSem` applies
to every x64 program with a semantic fault-freedom theorem
(`LiveOkStepsX64Locks.lean` for the published ones).
-/
import Kraken.Promising.X64
import Kraken.Promising.LiveOkSteps

namespace Kraken.Promising.X64

open Kraken Kraken.Promising

variable {A : Arch} {tid : Nat} {iv : InstrViews}

theorem loadPieces_total {σ : Type} {ds : Decls} {dmem : DataMem} :
    ∀ (n : Nat) {addr : BitVec 64} {k : List UInt8 → EvTree σ}, (∀ bs, (k bs).Total A tid iv) →
      (loadPieces ds dmem addr n k).Total A tid iv
  | 0, _, _, hk => hk []
  | n + 1, addr, k, hk => by
    simp only [loadPieces]
    split
    · exact loadPieces_total n fun _ => hk _
    · split
      · exact .fault _
      · exact .access fun _ => .load fun _ => loadPieces_total n fun _ => hk _

theorem storePieces_total {σ : Type} {ds : Decls} :
    ∀ (n : Nat) {addr : BitVec 64} {bs : List UInt8} {dmem : DataMem} {k : DataMem → EvTree σ},
      (∀ dmem, (k dmem).Total A tid iv) → (storePieces ds addr n bs dmem k).Total A tid iv
  | 0, _, _, _, _, hk => hk _
  | n + 1, addr, bs, dmem, k, hk => by
    simp only [storePieces]
    split
    · exact storePieces_total n hk
    · split
      · exact .fault _
      · exact .access fun _ => .store fun _ => storePieces_total n hk

/-- **Every x64 event tree is total.** -/
theorem toEv_total (ds : Decls) (e : Effects) : (toEv ds e).Total A tid iv := by
  induction e with
  | done => exact .done _
  | unimplemented => exact .fault _
  | syscall => exact .fault _
  | gp_unaligned => exact .fault _
  | nonmem_load _ _ _ _ ih => exact .access fun _ => .load fun _ => ih _ _
  | nonmem_store _ _ _ _ ih => exact .access fun _ => .store fun _ => ih _
  | undefined ret ih =>
    rename_i α inst
    cases inst with
    | bool => exact .choose (by decide) fun _ => ih _
    | bitvec => exact .fault _
    | avx_bitvec => exact .fault _
    | statusFlags => exact .fault _
  | require_read_access _ _ _ ih => exact ih _
  | require_write_access _ _ _ ih => exact ih _
  | require_exec_access _ _ ih => exact ih _
  | sync_load _ _ _ _ _ _ ih => exact .access fun _ => .load fun _ => ih _ _
  | sync_store _ _ _ _ _ _ ih => exact .access fun _ => .store fun _ => ih _ _
  | rmw _ _ _ _ _ _ ih => exact .access fun _ => .rmw fun _ => ih _ _
  | fence _ _ ih => exact .fence (ih _)
  | require_read_access_avx _ _ _ _ ih => exact ih _
  | require_write_access_avx _ _ _ _ ih => exact ih _
  | nonmem_load_avx _ _ _ _ _ ih =>
    simp only [toEv]
    split
    · exact .access fun _ => .load fun _ => ih _ _
    · exact loadPieces_total _ fun _ => ih _ _
  | nonmem_store_avx _ _ _ _ _ ih =>
    simp only [toEv]
    split
    · exact .access fun _ => .store fun _ => ih _
    · exact storePieces_total _ fun _ => ih _
  | rmw16 _ _ _ _ _ ih => exact .access fun _ => .rmw fun _ => ih _ _

/-- **Every instruction tree of `X64.isa` is total.** -/
instance : isa.ExecTotal where
  total A tid iv s tree h := by
    simp only [isa, exec] at h
    split at h
    · cases h
    · cases h; exact .map _ (toEv_total _ _)

end Kraken.Promising.X64
