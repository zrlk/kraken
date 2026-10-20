/-
**Part 4: the x64 instance of the Treiber
VCs** (`EnvG/TreiberVCCommon.lean` at `I := X64.isa`, `A := Arch.tso`).

- **Parameters** `tParamsX t n tok`: `top = ⟨t, 8⟩`, the node's data word
  `n1d = ⟨n, 4⟩` and link word `n1n = ⟨n + 8, 8⟩`, the ghost token `tok`
  (the Treiber proof's `tParams`, restated: that one lives in an AArch64 file); an
  alias of the neutral `TreiberCommon.tParamsC`.
- **The `lock cmpxchgq` operation** `cmpxOp64 x y` (`MachineWP.lock_cmpxchg_shared_spec`:
  expected `rax = x`, new `y`) is a compare-and-swap (`cmpxOp64_casMatch`).
- **Layouts.** The x64 environments are restricted to a layout of shared
  locations (`EnvGCX … S`: every access must be exactly a location of `S`,
  also outside the clean flag). The pusher's accesses are at fixed addresses
  (`pushS t n`: `top`, `n1d`, `n1n`). The popper's `movq 8(%rax), %rcx` and
  `movl (%rax), %r11d` are at a *loaded* address, which only the clean flag
  pins to `n1`; so the popper's layout is `sAll`, every 4- and 8-byte
  location, with a private memory that maps nothing (`Split sAll` holds
  exactly when no byte is mapped). `sAll` is irreducible (2 ^ 65 entries);
  use `mem_sAll4`, `mem_sAll8`, `sAll_le16`.
- **Environments** `EPX` (pusher, thread `0`, `pushPlan`, `pushS`) and `EQX`
  (popper, thread `1`, `popPlan`, `sAll`).
-/
import Kraken.Promising.SLR.EnvG.TreiberVCCommon
import Kraken.Promising.SLR.EnvG.X64RmwGhostVCGen
import Kraken.Promising.SLR.EnvG.X64TreiberSmoke

namespace Kraken.Promising.X64.EnvG.TreiberX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon

/-! ## Parameters, operation, layouts, environments -/

/-- The parameters of the x64 `treiber_pp.kl` at `top = t` (8 bytes) and the
node `n1 = n` (data word `[n]`, 4 bytes; link `[n + 8]`, 8 bytes), with the
ghost token `tok`: the ISA-neutral `TreiberCommon.tParamsC` (same
type). An `abbrev` rather than a `hoist_alias`, because `TreiberX.tPX` is
compiled and `hoist_alias` definitions are not. -/
abbrev tParamsX (t n : BitVec 64) (tok : Loc) : Params := tParamsC t n tok

/-- The operation of `lock cmpxchgq %r, d(%b)` with `rax = x`, `r = y`. -/
abbrev cmpxOp64 (x y : BitVec 64) : Val → Option Val :=
  rmwOp128 .W64 fun o => if o == x then some y else none

theorem cmpxOp64_casMatch (x y : BitVec 64) : CasMatch (cmpxOp64 x y) x y where
  some o n h := by
    simp only [rmwOp128, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    split at ha
    · next h0 => exact ⟨by simpa using h0, by cases ha; rfl⟩
    · cases ha
  none o h h0 := by
    simp [rmwOp128, h0] at h

/-- The pusher's shared layout: `top`, the node's data and link words. -/
abbrev pushS (t n : BitVec 64) : SharedEnv.Layout := [(t, 8), (n, 4), (n + 8, 8)]

theorem pushS_le16 (t n : BitVec 64) : Le16 (pushS t n) := fun x hx => by
  simp only [pushS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-- **Every 4- and 8-byte location**: the popper's shared layout (its loads
of `next` and of the data word are at a loaded address). -/
@[irreducible] def sAll : SharedEnv.Layout :=
  (List.range (2 ^ 64)).flatMap fun i => [(BitVec.ofNat 64 i, 4), (BitVec.ofNat 64 i, 8)]

theorem mem_sAll4 (a : BitVec 64) : (a, 4) ∈ sAll := by
  unfold sAll
  exact List.mem_flatMap.mpr ⟨a.toNat, List.mem_range.mpr a.isLt, by simp⟩

theorem mem_sAll8 (a : BitVec 64) : (a, 8) ∈ sAll := by
  unfold sAll
  exact List.mem_flatMap.mpr ⟨a.toNat, List.mem_range.mpr a.isLt, by simp⟩

theorem sAll_le16 : Le16 sAll := fun x hx => by
  unfold sAll at hx
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp

/-- `Split sAll` holds of a private memory that maps no byte. -/
theorem split_sAll {d : DataMem} (h : ∀ k, d.get? k = none) : Split sAll d := fun k _ => h k

/-- The pusher's environment (thread `0`). -/
abbrev EPX (t n : BitVec 64) (tok : Loc) : SharedEnv := EnvGCX Arch.tso 0 (pushPlan (tParamsX t n tok)) (pushS t n)

/-- The popper's environment (thread `1`). -/
abbrev EQX (t n : BitVec 64) (tok : Loc) : SharedEnv := EnvGCX Arch.tso 1 (popPlan (tParamsX t n tok)) sAll

theorem tso_plain_not_nt : Arch.tso.storeKind .plain ≠ .nt := by decide

/-! ## The VCs at the x64 environments, at addresses and operations given by
equations (the form `vcgen` goals take) -/

section At

variable {t n : BitVec 64} {tok : Loc} {a : BitVec 64}

theorem vc_push_str_d_ok_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu0 (tParamsX t n tok) σ)
    {v : Val} (ha : a = n) (hv : v = 1#128) : (EPX t n tok).ok (.store .plain false a 4 v) σ := by
  subst ha
  exact ⟨(vc_push_str_d hL tso_plain_not_nt σ h v hv).1, by simp [SharedEnv.AccessIn]⟩

theorem vc_push_str_d_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu0 (tParamsX t n tok) σ)
    {v : Val} (ha : a = n) (hv : v = 1#128) :
    ∀ b (σ' : EStateX), (EPX t n tok).step (.store .plain false a 4 v) σ b σ' → Pu (tParamsX t n tok) σ' := by
  subst ha
  exact (vc_push_str_d hL tso_plain_not_nt σ h v hv).2

theorem vc_push_load_at (σ : EStateX) (h : Pu (tParamsX t n tok) σ) {k : LoadKind} {xcl : Bool} {m : Nat} :
    ∀ v (σ' : EStateX), (EPX t n tok).step (.load k xcl a m) σ v σ' → Pu (tParamsX t n tok) σ' :=
  vc_push_load σ h

theorem vc_push_str_n_ok_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu (tParamsX t n tok) σ)
    (v : Val) (ha : a = n + 8) : (EPX t n tok).ok (.store .plain false a 8 v) σ := by
  subst ha
  exact ⟨(vc_push_str_n hL σ h v).1, by simp [SharedEnv.AccessIn]⟩

theorem vc_push_str_n_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu (tParamsX t n tok) σ)
    (v : Val) (ha : a = n + 8) :
    ∀ b (σ' : EStateX), (EPX t n tok).step (.store .plain false a 8 v) σ b σ' → Pu (tParamsX t n tok) σ' := by
  subst ha
  exact (vc_push_str_n hL σ h v).2

theorem vc_push_cas_ok_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu (tParamsX t n tok) σ)
    (x2 : BitVec 64) {op : Val → Option Val} (ha : a = t) (hop : op = cmpxOp64 x2 n) :
    (EPX t n tok).ok (.rmw .acqRel a 8 op) σ := by
  subst ha hop
  exact ⟨(vc_push_cas hL σ h x2 n rfl (cmpxOp64_casMatch x2 n)).1, by simp [SharedEnv.AccessIn]⟩

theorem vc_push_cas_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pu (tParamsX t n tok) σ)
    (x2 : BitVec 64) {op : Val → Option Val} (ha : a = t) (hop : op = cmpxOp64 x2 n) :
    ∀ old (σ' : EStateX), (EPX t n tok).step (.rmw .acqRel a 8 op) σ old σ' →
      (BitVec.setWidth 64 old ≠ x2 ∧ Pu (tParamsX t n tok) σ') ∨
        (BitVec.setWidth 64 old = x2 ∧ Pd (tParamsX t n tok) σ') := by
  subst ha hop
  exact (vc_push_cas hL σ h x2 n rfl (cmpxOp64_casMatch x2 n)).2

theorem vc_pop_load_at (σ : EStateX) (h : Pp (tParamsX t n tok) σ) {k : LoadKind} {xcl : Bool} {m : Nat} :
    ∀ v (σ' : EStateX), (EQX t n tok).step (.load k xcl a m) σ v σ' → Pp (tParamsX t n tok) σ' :=
  vc_pop_load σ h

theorem vc_pop_cas_ok_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pp (tParamsX t n tok) σ)
    (x2 x4 : BitVec 64) (hx2 : x2 ≠ 0) {op : Val → Option Val} (ha : a = t) (hop : op = cmpxOp64 x2 x4) :
    (EQX t n tok).ok (.rmw .acqRel a 8 op) σ := by
  subst ha hop
  exact ⟨(vc_pop_cas hL σ h x2 x4 hx2 (cmpxOp64_casMatch x2 x4)).1, mem_sAll8 _⟩

theorem vc_pop_cas_at (hL : TLocs (tParamsX t n tok)) (σ : EStateX) (h : Pp (tParamsX t n tok) σ)
    (x2 x4 : BitVec 64) (hx2 : x2 ≠ 0) {op : Val → Option Val} (ha : a = t) (hop : op = cmpxOp64 x2 x4) :
    ∀ old (σ' : EStateX), (EQX t n tok).step (.rmw .acqRel a 8 op) σ old σ' →
      (BitVec.setWidth 64 old ≠ x2 ∧ Pp (tParamsX t n tok) σ') ∨
        (BitVec.setWidth 64 old = x2 ∧ Pc (tParamsX t n tok) x2 σ') := by
  subst ha hop
  exact (vc_pop_cas hL σ h x2 x4 hx2 (cmpxOp64_casMatch x2 x4)).2

theorem vc_pop_ldr_at (σ : EStateX) (x2 : BitVec 64) (h : Pc (tParamsX t n tok) x2 σ) {k : LoadKind}
    (ha : a = x2) :
    ∀ v (σ' : EStateX), (EQX t n tok).step (.load k false a 4) σ v σ' →
      (σ'.cl → n = x2 ∧ BitVec.setWidth 32 v = 1) := by
  subst a
  intro v σ' hs hc
  have := vc_pop_ldr (P := tParamsX t n tok) (by simp [tParamsX, tParamsC]) σ x2 h v σ' hs hc
  simpa [tParamsX, tParamsC] using this

end At

end Kraken.Promising.X64.EnvG.TreiberX
