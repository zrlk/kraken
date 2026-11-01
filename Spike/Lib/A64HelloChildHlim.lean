/-
**The child segment's stack-limit premises** (AArch64, row B8-seg-hlim; `Hello.SegR.ChildPrem`'s `hlimT`,
`hlimW`). The child thread's TCB limit word `tls + 8` is the runtime's, mapped for reading, off the handed
range `r1` (so unmapped in the child's first memory: `childAfter` copies only `r1`), and every value runtime
memory may hold there is at least the stub's and `wc_worker`'s frames (`80 + 96` bytes) below `r1`'s top.
From these, both premises at the stub's region `childR (r1.lo + r1.size) (-272)` (`Rt.childStub_hlim`).

- `hlimT_of`: `ChildPrem.hlimT` at thread pointer `tls`, entry stack `r1.lo + r1.size`.
- `hlimW_of`: `ChildPrem.hlimW` there (`wcJE` fixes the thread pointer; `SP` is the entry stack less 80).
- `hlim_stack`: both at the clone's `stack`, from the held list's first entry.
-/
import Spike.Lib.Rt.A64RtChildPrem
import Spike.Lib.A64HelloChild
import Spike.Lib.A64WakeChildAt

namespace Spike.Lib.HelloChildHlim

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow (tcbA DFrame)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.Child (wcJE Words)

variable {M : MemSide isaLSE2} {x : KState} {tid : Nat} {t : Thread isaLSE2} {r1 : Range} {tls : Nat}

/-- **`ChildPrem.hlimT`** at the thread pointer `tls` and entry stack `r1.lo + r1.size`, under the frame
of the child's first memory on the stub's region: the limit word off `r1` (`hout`), the runtime's (`hrt`),
mapped for reading (`hmp`), its values at most `r1`'s top less `176` (`hG`). -/
theorem hlimT_of (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : 272 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64) (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size) :
    ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      M.rt (tcbA r 8).toNat ∧ M.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, M.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 (r1.lo + r1.size) - (80 : Int64).toBitVec).toNat := by
  intro r hr
  obtain ⟨h1, h2, h3, -⟩ := Spike.Lib.A64.Rt.childStub_hlim (lo := -272) hh htop (by omega) htls hout
    (by omega) hrt hmp (fun v hv => by have := hG v hv; omega) r hr
  refine ⟨h1, h2, h3, fun v hv => ?_⟩
  have hb : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  have e80 : (BitVec.ofNat 64 (r1.lo + r1.size) - (80 : Int64).toBitVec).toNat = r1.lo + r1.size - 80 := by
    rw [BitVec.toNat_sub, hb, show ((80 : Int64).toBitVec).toNat = 80 from rfl]; omega
  rw [Spike.Lib.A64.Rt.tcbA_ofNat hr] at hv
  have := hG v hv
  rw [e80]; omega

/-- **`ChildPrem.hlimW`** at the thread pointer `tls` and entry stack `r1.lo + r1.size` (`hlimT_of`'s
premises): `wcJE` fixes the thread pointer, and with `SP` the entry stack less `80` the bound is `SP - 96`. -/
theorem hlimW_of (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : 272 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64) (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size)
    {c0 : Spike.Lib.Ctl} {w : Words} :
    ∀ x29 ra σ c, wcJE c0 w x29 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.SP.toBitVec = BitVec.ofNat 64 (r1.lo + r1.size) - (80 : Int64).toBitVec →
      M.rt (tcbA σ.regs 8).toNat ∧ M.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, M.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat := by
  intro x29 ra σ c hJ hsp
  have htp : σ.regs.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls := hJ.2.2.2.2.2.2.2.2.2
  obtain ⟨h1, h2, h3, -⟩ := hlimT_of (t := t) hh htop hsz htls hout hrt hmp hG σ.regs htp
  refine ⟨h1, h2, h3, fun v hv => ?_⟩
  have hb : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  have e : (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat = r1.lo + r1.size - 176 := by
    rw [hsp, BitVec.toNat_sub, BitVec.toNat_sub, hb, show ((80 : Int64).toBitVec).toNat = 80 from rfl,
      show ((96 : Int64).toBitVec).toNat = 96 from rfl]
    omega
  rw [Spike.Lib.A64.Rt.tcbA_ofNat htp] at hv
  have := hG v hv
  rw [e]; omega

/-! ## At the clone's stack and held list -/

/-- **`ChildPrem.hlimT` and `hlimW` at the clone's `stack`**, the handed range `r1` ending there and held for
`tid` first (as at hello's clone: `held = [(0, r1c), (0, r0)]`, `HelloSpawnR.PreRH`'s `held` and `top`). -/
theorem hlim_stack {r0 : Range} {stack : Nat} (hst : r1.lo + r1.size = stack)
    (hheld : x.held = [(tid, r1), (tid, r0)]) (htop : r1.lo + r1.size < 2 ^ 64)
    (hsz : 272 ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64) (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8)
    (hrt : M.rt (tls + 8)) (hmp : M.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, M.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 176 ≤ r1.lo + r1.size) :
    (∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      M.rt (tcbA r 8).toNat ∧ M.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, M.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 stack - (80 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w : Words} x29 ra σ c, wcJE c0 w x29 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.SP.toBitVec = BitVec.ofNat 64 stack - (80 : Int64).toBitVec →
      M.rt (tcbA σ.regs 8).toNat ∧ M.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, M.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat := by
  subst hst
  have hh : handed x tid (r1.lo + r1.size) = some (tid, r1) := by simp [handed, hheld]
  exact ⟨hlimT_of hh htop hsz htls hout hrt hmp hG,
    fun {_ _} => hlimW_of hh htop hsz htls hout hrt hmp hG⟩

end Spike.Lib.HelloChildHlim

/-- info: 'Spike.Lib.HelloChildHlim.hlimT_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildHlim.hlimT_of

/-- info: 'Spike.Lib.HelloChildHlim.hlimW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildHlim.hlimW_of

/-- info: 'Spike.Lib.HelloChildHlim.hlim_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildHlim.hlim_stack
