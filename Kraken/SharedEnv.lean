/-
The ISA-free core of the environment-aware wp (design note
`Kraken/Promising/EnvWP.md`).

- `SharedAccess`, `SharedEnv`: the interface between a thread and its
  environment. Values are 128-bit payloads with an explicit byte count (1, 2, 4, 8 or 16),
  so the interface depends on neither ISA nor on the Promising machine's
  `Loc`/`Val`.
- `SharedEnv.LoadPieces`/`StorePieces` and `piecesNat`/`ofPieces`/`toPieces`:
  a non-atomic wide access as 8-byte pieces in address order.
- `SharedEnv.FenceInv`, `SharedEnv.FencesSkip`: the side condition of the
  lifting theorem; `SharedEnv.Skips`, `FencesSkip` as a class, for the
  generic `vcgen` rule of each ISA's `EnvVCGen`.
- `SharedEnv.none` (no shared locations) and `SharedEnv.lastWrite` (the
  one-thread instance, shape (i)).

Each ISA's `EnvWP` (`Kraken/EnvWP.lean` for x64, `Kraken/AArch64/EnvWP.lean`)
imports this file and adds `Effects.AllEnv`, the step relation, the wp and
the lifting theorem over its own `Effects`.
-/
import Kraken.MemKinds

open Kraken

namespace Kraken

/-! ## The interface -/

/-- One access to the environment, as the thread issues it. `bytes` is the
access width (1, 2, 4, 8 or 16; an 8-byte piece of a wider non-atomic vector
access is a `load`/`store` of 8). A stored value is the payload at its width,
zero-extended to 128 bits. An `rmw`'s `op` maps the old value to the value
written, or `none` when nothing is written (a failed compare). -/
inductive SharedAccess where
  | load (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (bytes : Nat)
  | store (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (bytes : Nat) (v : BitVec 128)
  | rmw (k : RmwKind) (addr : BitVec 64) (bytes : Nat) (op : BitVec 128 → Option (BitVec 128))
  | fence (k : FenceKind)

/-- What an access returns to the thread: the value read (`load`, the old
value of an `rmw`), the success of a store (always `true` unless exclusive),
nothing for a fence. -/
abbrev SharedAccess.Ret : SharedAccess → Type
  | .load .. => BitVec 128
  | .store .. => Bool
  | .rmw .. => BitVec 128
  | .fence _ => Unit

/-- An environment: the thread's view of everything outside its `dmem`.

- `State`: the environment state the thread's proof tracks (in the one-thread
  instance the shared values; in a thread-modular proof the thread's ghost
  state and knowledge, e.g. "I hold the lock").
- `ok a g`: the thread may issue `a` in `g` — the **guarantee** (what the
  thread may write) and the access discipline (which addresses and widths are
  shared locations). `AllEnv` requires it at every access.
- `step a g r g'`: issuing `a` in `g` may return `r` and move to `g'` — the
  **rely** (what values the other threads may have left). `AllEnv` quantifies
  over every outcome.

Interference by other threads is not a separate step: it is folded into the
outcomes `step` allows, so `State` changes only at the thread's own accesses
and fences. That is what makes the lifting theorem free. -/
structure SharedEnv where
  State : Type
  ok : SharedAccess → State → Prop
  step : (a : SharedAccess) → State → a.Ret → State → Prop

namespace SharedEnv

/-- The pieces of a non-atomic access, read in address order: `n` plain
8-byte loads from `addr`, `addr + 8`, …, each permitted and answered by the
environment; `k` receives the pieces in address order. -/
def LoadPieces (env : SharedEnv) (addr : BitVec 64) :
    Nat → env.State → (List (BitVec 64) → env.State → Prop) → Prop
  | 0, g, k => k [] g
  | n + 1, g, k => env.ok (.load .plain false addr 8) g ∧
      ∀ v g', env.step (.load .plain false addr 8) g v g' →
        LoadPieces env (addr + 8) n g' (fun vs g'' => k (v.setWidth 64 :: vs) g'')

/-- The pieces of a non-atomic store, written in address order. -/
def StorePieces (env : SharedEnv) (addr : BitVec 64) :
    List (BitVec 64) → env.State → (env.State → Prop) → Prop
  | [], g, k => k g
  | p :: ps, g, k => env.ok (.store .plain false addr 8 (p.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr 8 (p.setWidth 128)) g b g' →
        StorePieces env (addr + 8) ps g' k

end SharedEnv

/-- The value of 8-byte pieces in address order, little-endian. -/
def piecesNat : List (BitVec 64) → Nat
  | [] => 0
  | v :: vs => v.toNat + 2 ^ 64 * piecesNat vs

/-- A `m`-bit value assembled from its 8-byte pieces. -/
def ofPieces (m : Nat) (vs : List (BitVec 64)) : BitVec m := BitVec.ofNat m (piecesNat vs)

/-- The first `n` 8-byte pieces of a value, in address order. -/
def toPieces {m : Nat} (v : BitVec m) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun i => v.extractLsb' (64 * i) 64)

/-- An `rmw`'s operation on an `n`-bit location, on 128-bit payloads: the
old value truncated to `n` bits, the new value zero-extended. (x64's
`rmwOp128` is this at a `Width`; AArch64 uses it at `MemWidth.bits`.) -/
def rmwOpBits (n : Nat) (op : BitVec n → Option (BitVec n)) : BitVec 128 → Option (BitVec 128) :=
  fun x => (op (x.setWidth n)).map (·.setWidth 128)

end Kraken

namespace Kraken.SharedEnv

/-- `I` is an invariant of the environment state that every fence permits and
preserves. Fences are the only effects `All` lets through that `AllEnv`
hands to the environment. -/
def FenceInv (env : SharedEnv) (I : env.State → Prop) : Prop :=
  ∀ k g, I g → env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → I g'

/-- Fences are permitted and change nothing. -/
def FencesSkip (env : SharedEnv) : Prop :=
  ∀ k g, env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → g' = g

theorem FencesSkip.fenceInv_eq {env : SharedEnv} (h : env.FencesSkip) (g₀ : env.State) :
    env.FenceInv (· = g₀) :=
  fun k g hg => ⟨(h k g).1, fun g' hs => ((h k g).2 g' hs).trans hg⟩

theorem FencesSkip.fenceInv_true {env : SharedEnv} (h : env.FencesSkip) :
    env.FenceInv (fun _ => True) :=
  fun k g _ => ⟨(h k g).1, fun _ _ => trivial⟩

/-- `FencesSkip` as a class: the instance argument of the generic `vcgen`
rule (`MachineWP.env_lift_spec` in each ISA's `EnvVCGen`), which `vcgen`
synthesises at every instruction. -/
class Skips (env : SharedEnv) : Prop where
  fencesSkip : env.FencesSkip

end Kraken.SharedEnv

/-! ## Two environments -/

namespace Kraken.SharedEnv

/-- No shared locations: every access outside `dmem` is refused, fences are
permitted and change nothing. -/
def none : SharedEnv where
  State := Unit
  ok a _ := match a with
    | .fence _ => True
    | _ => False
  step a _ _ _ := match a with
    | .fence _ => True
    | _ => False

theorem none_fencesSkip : none.FencesSkip := fun _ _ => ⟨trivial, fun _ _ => rfl⟩

instance : none.Skips := ⟨none_fencesSkip⟩

/-- The shared locations of a one-thread run: address and width in bytes (the
shape of `Kraken.Promising.SharedLayout`). -/
abbrev Layout := List (BitVec 64 × Nat)

/-- `g` with the value at `addr` replaced by `v`. -/
def upd (g : BitVec 64 → BitVec 128) (addr : BitVec 64) (v : BitVec 128) : BitVec 64 → BitVec 128 :=
  fun k => if k = addr then v else g k

@[simp] theorem upd_same (g : BitVec 64 → BitVec 128) (addr : BitVec 64) (v : BitVec 128) :
    upd g addr v addr = v := if_pos rfl

@[simp] theorem upd_ne {g : BitVec 64 → BitVec 128} {addr k : BitVec 64} (v : BitVec 128)
    (h : k ≠ addr) : upd g addr v k = g k := if_neg h

/-- The one-thread instance, shape (i) of the design: the environment is the
last write to each shared location. Its state is the value of each location
(by address); an access must be exactly a location of `L` at its width; a load
returns the location's value; a store or `rmw` replaces it; a store-exclusive
may also fail and change nothing. -/
def lastWrite (L : Layout) : SharedEnv where
  State := BitVec 64 → BitVec 128
  ok a _ := match a with
    | .load _ _ addr n => (addr, n) ∈ L
    | .store _ _ addr n _ => (addr, n) ∈ L
    | .rmw _ addr n _ => (addr, n) ∈ L
    | .fence _ => True
  step a g r g' := match a, r with
    | .load _ _ addr _, v => v = g addr ∧ g' = g
    | .store _ xcl addr _ v, b =>
      (b = true ∧ g' = SharedEnv.upd g addr v) ∨ (xcl = true ∧ b = false ∧ g' = g)
    | .rmw _ addr _ op, old =>
      old = g addr ∧ g' = match op old with
        | some v => SharedEnv.upd g addr v
        | Option.none => g
    | .fence _, _ => g' = g

theorem lastWrite_fencesSkip (L : Layout) : (lastWrite L).FencesSkip :=
  fun _ _ => ⟨trivial, fun _ h => h⟩

instance (L : Layout) : (lastWrite L).Skips := ⟨lastWrite_fencesSkip L⟩

/-- `upd_same` at a `lastWrite` state (whose type `simp` does not unfold). -/
@[simp] theorem lastWrite_upd_same (L : Layout) (g : (lastWrite L).State) (addr : BitVec 64)
    (v : BitVec 128) : upd g addr v addr = v := if_pos rfl

/-- `upd_ne` at a `lastWrite` state. -/
@[simp] theorem lastWrite_upd_ne (L : Layout) {g : (lastWrite L).State} {addr k : BitVec 64}
    (v : BitVec 128) (h : k ≠ addr) : upd g addr v k = g k := if_neg h

end Kraken.SharedEnv

/-! ## Tests: the pieces of a non-atomic vector access -/

/-- info: true -/
#guard_msgs in
#eval toPieces (0x22222222222222221111111111111111#128) 2 == [0x1111111111111111#64, 0x2222222222222222#64]

/-- info: true -/
#guard_msgs in
#eval ofPieces 128 (toPieces (0x22222222222222221111111111111111#128) 2)
  == 0x22222222222222221111111111111111#128

/-- info: true -/
#guard_msgs in
#eval ofPieces 256 [0x1111111111111111#64, 0x2222222222222222#64, 0x3333333333333333#64,
  0x4444444444444444#64] == 0x4444444444444444333333333333333322222222222222221111111111111111#256

/-! ## Tests: an `rmw`'s operation at a bit count -/

/-- info: true -/
#guard_msgs in
#eval rmwOpBits 8 (fun x => some (x + 1)) 0x1FF#128 == some 0#128

/-- info: true -/
#guard_msgs in
#eval rmwOpBits 64 (fun x => if x == 5 then some 7 else none) 5#128 == some 7#128

/-- info: true -/
#guard_msgs in
#eval rmwOpBits 64 (fun x => if x == 5 then some 7 else none) 6#128 == none
