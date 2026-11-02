/-
**The child's limit word from the second TCB's words on x86-64** (the twin of `Spike/Lib/A64HelloChildTls.lean`;
the hello twin of `Rt.PreChild.preChild_hlim`): `X64.HelloChildHlim.hlim_stack`'s five runtime premises at the
clone's thread pointer `tls` (`%r8`) from `Rt.PreChild.TcbArea` at the TCB `tcbOf lab q`, with `tls` that TCB and
the layout's bounds, gathered in one premise `TlsTcb`.

- `TlsTcb M lab q tls r1`: `TcbArea`, `tls = tcbOf lab q`, the limit word fitting and off `r1`, and `TcbArea`'s
  limit bound (`r1Of lab`'s base plus 4096) at least the two prologues' frames below `r1`'s top.
- `TlsTcb.hlim_a` .. `TlsTcb.hlim_e`: the five rows.
- `room_r1Of`: the frames' room at `r1 = r1Of lab` (the 16 KiB second take, wake's).
- An `example`: `TlsTcb` inhabited at a memory side allowing at the limit word exactly `TcbArea`'s bound.
- `TlsTcb.hlim_stack`: `X64.HelloChildHlim.hlim_stack` from `TlsTcb`.

## Differences from the AArch64 version

- `TcbArea`, `r1Of`, `tcbOf` and `ThreadInit.fields` are the x86-64 runtime's (`Spike/Lib/Rt/X64RtPreChild.lean`,
  same shape); the clone's thread pointer is `%r8` (A64: `x3`).
- `TlsTcb.hlim_stack` has `X64.HelloChildHlim.hlim_stack`'s shape: the prologues' `hedge` bounds against the
  entry `%rsp` (`stack - 8`, `stack - 88`), the region's depth `lo` a parameter (`-lo ≤ r1.size`, and
  `176 ≤ r1.size`; A64: `272 ≤ r1.size` at `childR stack (-272)`).
-/
import Spike.Lib.X64HelloChildHlim
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.HelloChildTls

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt (TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (TcbArea r1Of)

/-- **The clone's thread pointer is the second TCB, its words `TcbArea`'s**: `tls` the
TCB, its limit word `tls + 8` fitting in 64 bits and off the handed range `r1`, and `TcbArea`'s limit bound
leaving the stub's and `wc_worker`'s frames (`176` bytes) below `r1`'s top. -/
structure TlsTcb (M : MemSide isa) (lab : Label → Int64) (q : TcbGG) (tls : Nat) (r1 : Range) : Prop where
  area : TcbArea M lab q
  tls_eq : tls = (tcbOf lab q).toNat
  fit : tls + 16 ≤ 2 ^ 64
  out : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8
  room : (r1Of lab).lo + 4096 + 176 ≤ r1.lo + r1.size

namespace TlsTcb

variable {M : MemSide isa} {lab : Label → Int64} {q : TcbGG} {tls : Nat} {r1 : Range}

theorem e8 (h : TlsTcb M lab q tls r1) : tcbOf lab q + 8#64 = BitVec.ofNat 64 (tls + 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h.tls_eq]

/-- **The limit word fits in the address space**: `tls + 16 ≤ 2 ^ 64`. -/
theorem hlim_a (h : TlsTcb M lab q tls r1) : tls + 16 ≤ 2 ^ 64 := h.fit

/-- **The limit word is off the handed range `r1`.** -/
theorem hlim_b (h : TlsTcb M lab q tls r1) : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8 := h.out

/-- **The limit word is the runtime's** (`TcbArea.rt` at `scc_rt_thread_init`'s field 1). -/
theorem hlim_c (h : TlsTcb M lab q tls r1) : M.rt (tls + 8) := by
  have hrt := h.area.rt (tcbOf lab q + BitVec.ofNat 64 (8 * 1)) (by simp [Spike.Lib.X64.Rt.Ti.tiAddrs])
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from rfl, h.e8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := h.fit; omega)] at hrt
  exact hrt

/-- **The limit word is mapped for reading** (`TcbArea.mpR`). -/
theorem hlim_d (h : TlsTcb M lab q tls r1) : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false := by
  have := h.area.mpR
  rw [h.e8] at this
  exact this

/-- **The limit word's values fit below `r1`'s top**: every value at the limit word leaves the frames below
`r1`'s top (`TcbArea.lim`, `room`). -/
theorem hlim_e (h : TlsTcb M lab q tls r1) :
    ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size := by
  intro v hv
  rw [← h.e8] at hv
  have := h.area.lim v hv
  have := h.room
  omega

variable {x : KState} {tid : Nat} {t : Thread isa} {lo : Int}

/-- **`HelloChildHlim.hlim_stack` from `TlsTcb`**: both prologues' stack-limit facts at the clone's `stack`. -/
theorem hlim_stack (h : TlsTcb M lab q tls r1) {r0 : Range} {stack : Nat} (hst : r1.lo + r1.size = stack)
    (hheld : x.held = [(tid, r1), (tid, r0)]) (htop : r1.lo + r1.size < 2 ^ 64) (hsz : -lo ≤ r1.size)
    (h176 : 176 ≤ r1.size) :
    (∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      r.rsp.toBitVec = BitVec.ofNat 64 stack - 8#64 →
      M.rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 stack, lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (r.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w : Spike.Lib.X64.Flow.Worker.Hello.Child.Words} rbp0 ra σ c,
      Spike.Lib.X64.Flow.Worker.Hello.Child.wcJE c0 w rbp0 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.rsp.toBitVec = BitVec.ofNat 64 stack - 88#64 →
      M.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 stack, lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat :=
  Spike.Lib.X64.HelloChildHlim.hlim_stack hst hheld htop hsz h176 h.hlim_a h.hlim_b h.hlim_c h.hlim_d h.hlim_e

end TlsTcb

/-- **The frames' room at the second take `r1Of lab`** (16 KiB). -/
theorem room_r1Of (lab : Label → Int64) :
    (r1Of lab).lo + 4096 + 176 ≤ (r1Of lab).lo + (r1Of lab).size := by
  show _ ≤ _ + 16384
  omega

/-- `TlsTcb` is inhabited at any TCB whose limit word fits and lies off the second take: the memory side that
allows at the limit word exactly `TcbArea`'s bound and anything elsewhere. -/
example (lab : Label → Int64) (q : TcbGG) (hfit : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (r1Of lab).lo ∨ (r1Of lab).lo + (r1Of lab).size ≤ (tcbOf lab q).toNat + 8) :
    ∃ M : MemSide isa, TlsTcb M lab q (tcbOf lab q).toNat (r1Of lab) := by
  let M : MemSide isa :=
    { rd := fun _ => True, rt := fun _ => True, K := none,
      G := fun l v => l = ⟨tcbOf lab q + 8#64, 8⟩ → (v.setWidth 64).toNat ≤ (r1Of lab).lo + 4096,
      heap := 0, ctr := 0, units := fun _ _ => 0, off := fun _ _ => 0, cells := 0, mp := fun _ _ => True }
  refine ⟨M, ⟨⟨fun _ _ => trivial, fun _ _ => trivial, trivial, ?_, ?_, ?_, fun _ h => h rfl⟩, rfl, hfit, hout,
    room_r1Of lab⟩⟩
  · intro h
    simp only [Loc.mk.injEq, and_true] at h
    simp only [tcbOf] at h
    bv_omega
  · intro h
    simp only [Loc.mk.injEq, and_true] at h
    bv_omega
  · intro e he h
    simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Loc.mk.injEq, and_true] at h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h ⊢ <;> try bv_omega
    show _ ≤ (stacksA lab + 16384#64).toNat + 4096
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

end Spike.Lib.X64.HelloChildTls

/-- info: 'Spike.Lib.X64.HelloChildTls.TlsTcb.hlim_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloChildTls.TlsTcb.hlim_stack
