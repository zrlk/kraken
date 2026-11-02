/-
**The child segment's stack-limit premises on x86-64** (the twin of `Spike/Lib/A64HelloChildHlim.lean`): the
child thread's stack-limit word `%fs:8` (`tls + 8`) is the runtime's, mapped for reading, off the handed range
`r1` (so unmapped in the child's first memory: `childAfter` copies only `r1`), and every value runtime memory
may hold there is at least the two prologues' frames below `r1`'s top (`176` bytes: the child's `call` enters
`scc_rt_thr_worker` at `top - 8`, its check address is `top - 80`; `wc_worker` is entered at `top - 88`, its
check address `top - 176`). From these, both prologues' stack-limit facts at the stub's region
`⟨ofNat top, lo, 0⟩` (`Rt.childStub_hlim`).

- `hlimT_of`: `scc_rt_thr_worker`'s prologue's stack-limit facts at thread pointer `tls`, entry `%rsp`
  `top - 8`, in the shape of `thr_prologue_segNN`'s `hedge`.
- `hlimW_of`: `wc_worker`'s at entry `%rsp` `top - 88` (`wcJE` fixes the thread pointer), in the shape of
  `wc_prologue_segNN`'s `hedge`.
- `hlim_stack`: both at the clone's `stack`, from the held list's first entry.

## Differences from the AArch64 version

- The thread pointer is `fsBase` and the limit word `fsBase + 8` (A64: `TPIDR_EL0`, `tcbA r 8`); the bounds
  are stated against the entry `%rsp` as the x86-64 prologue's `hedge` reads them (`rsp - 8 - Z`, `Z` = 64
  and 80), with the entry `%rsp` a premise (`top - 8`, `top - 88`); A64 states the thread worker's against
  the constant `top - 80` and `wc_worker`'s against `SP - 96` with `SP = top - 80`. The total, 176 bytes, is
  the same.
- The region's depth `lo` is a parameter (`-lo ≤ r1.size`; A64 fixes `-272`), and the frame is
  `Spike.Lib.X64.DFrame` of the literal region (as `Rt.childStub_hlim`); no alignment premise.
-/
import Spike.Lib.Rt.X64RtChildPrem
import Spike.Lib.X64HelloChild
import Spike.Lib.X64WakeChildAt

namespace Spike.Lib.X64.HelloChildHlim

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.X64.Flow.Worker.Hello.Child (wcJE Words)

variable {M : MemSide isa} {x : KState} {tid : Nat} {t : Thread isa} {r1 : Range} {tls : Nat} {lo : Int}

/-- `ofNat top - k`, for `k ≤ top < 2 ^ 64`, is `top - k`. -/
private theorem toNat_ofNat_sub {top k : Nat} (htop : top < 2 ^ 64) (hk : k ≤ top) :
    (BitVec.ofNat 64 top - BitVec.ofNat 64 k).toNat = top - k := by
  have ht : (BitVec.ofNat 64 top).toNat = top := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  have hk' : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ht, hk']; exact hk), ht, hk']

/-- **`scc_rt_thr_worker`'s stack-limit facts** at the thread pointer `tls` and entry `%rsp` `top - 8`
(`top = r1.lo + r1.size`), under the frame of the child's first memory on the stub's region: the limit word
off `r1` (`hout`), the runtime's (`hrt`), mapped for reading (`hmp`), its values at most `top - 176`
(`hG`). -/
theorem hlimT_of (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : -lo ≤ r1.size) (h176 : 176 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size) :
    ∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      r.rsp.toBitVec = BitVec.ofNat 64 (r1.lo + r1.size) - 8#64 →
      M.rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (r.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat := by
  intro r hr hsp
  obtain ⟨h1, h2, h3, -⟩ := Spike.Lib.X64.Rt.childStub_hlim (lo := lo) (t := t) hh htop hsz htls hout
    (by omega) hrt hmp (fun v hv => by have := hG v hv; omega) r hr
  refine ⟨h1, h2, h3, fun v hv => ?_⟩
  rw [Spike.Lib.X64.Rt.tcbA_ofNat hr] at hv
  have := hG v hv
  have e : (r.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat = r1.lo + r1.size - 80 := by
    rw [hsp, BitVec.sub_sub, BitVec.sub_sub]
    exact toNat_ofNat_sub (k := 80) htop (by omega)
  rw [e]; omega

/-- **`wc_worker`'s stack-limit facts** at the thread pointer `tls` and entry `%rsp` `top - 88`
(`hlimT_of`'s premises): `wcJE` fixes the thread pointer, and the bound is `rsp - 8 - 80 = top - 176`. -/
theorem hlimW_of (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : -lo ≤ r1.size) (h176 : 176 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size)
    {c0 : Spike.Lib.Ctl} {w : Words} :
    ∀ rbp0 ra σ c, wcJE c0 w rbp0 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.rsp.toBitVec = BitVec.ofNat 64 (r1.lo + r1.size) - 88#64 →
      M.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat := by
  intro rbp0 ra σ c hJ hsp
  have htp : σ.regs.fsBase.toBitVec = BitVec.ofNat 64 tls := hJ.2.2.2.2.2.2.2.2.2
  obtain ⟨h1, h2, h3, -⟩ := Spike.Lib.X64.Rt.childStub_hlim (lo := lo) (t := t) hh htop hsz htls hout
    (by omega) hrt hmp (fun v hv => by have := hG v hv; omega) σ.regs htp
  refine ⟨h1, h2, h3, fun v hv => ?_⟩
  rw [Spike.Lib.X64.Rt.tcbA_ofNat htp] at hv
  have := hG v hv
  have e : (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat = r1.lo + r1.size - 176 := by
    rw [hsp, BitVec.sub_sub, BitVec.sub_sub]
    exact toNat_ofNat_sub (k := 176) htop (by omega)
  rw [e]; omega

/-! ## At the clone's stack and held list -/

/-- **Both prologues' stack-limit facts at the clone's `stack`**, the handed range `r1` ending there and held
for `tid` first (as at hello's clone: `held = [(0, r1c), (0, r0)]`). -/
theorem hlim_stack {r0 : Range} {stack : Nat} (hst : r1.lo + r1.size = stack)
    (hheld : x.held = [(tid, r1), (tid, r0)]) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : -lo ≤ r1.size) (h176 : 176 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size) :
    (∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      r.rsp.toBitVec = BitVec.ofNat 64 stack - 8#64 →
      M.rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 stack, lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (r.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w : Words} rbp0 ra σ c, wcJE c0 w rbp0 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.rsp.toBitVec = BitVec.ofNat 64 stack - 88#64 →
      M.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      M.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 stack, lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, M.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat := by
  subst hst
  have hh : handed x tid (r1.lo + r1.size) = some (tid, r1) := by simp [handed, hheld]
  exact ⟨hlimT_of hh htop hsz h176 htls hout hrt hmp hG,
    fun {_ _} => hlimW_of hh htop hsz h176 htls hout hrt hmp hG⟩

end Spike.Lib.X64.HelloChildHlim

/-- info: 'Spike.Lib.X64.HelloChildHlim.hlimT_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloChildHlim.hlimT_of

/-- info: 'Spike.Lib.X64.HelloChildHlim.hlimW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloChildHlim.hlimW_of

/-- info: 'Spike.Lib.X64.HelloChildHlim.hlim_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloChildHlim.hlim_stack
