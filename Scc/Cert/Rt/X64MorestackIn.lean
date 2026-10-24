import Scc.Cert.Rt.CodeX64
import Scc.Cert.Rt.X64Morestack

/-!
# `scc_rt_morestack` in an emitted x64 program

`Scc.Cert.Rt.X64.Morestack.seg_morestack` takes the layout of
`scc_rt_morestack` as a hypothesis `Code exe endPc`: each of its five blocks
at its byte offset from the label. `morestackIn cells` checks them on the
code cells (`blockAtB`), and `code_morestack` is `Code` in any valid layout
of code cells with `morestackIn cells = true`.
-/

namespace Scc.Cert.Rt.X64.Morestack

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

/-- **The code of `scc_rt_morestack` in `cells`**: its blocks at their
byte offsets from the label. -/
def morestackIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "scc_rt_morestack" 0 b0 &&
  blockAtB cells "scc_rt_morestack" 15 b1 &&
  blockAtB cells "scc_rt_morestack" 18 [(swDir .rbp, 3)] &&
  blockAtB cells "scc_rt_morestack" 21 b2 &&
  blockAtB cells "scc_rt_morestack" 32 b3

/-- **The layout of `scc_rt_morestack`** in any valid layout `exe` of code
cells `cells` with `morestackIn cells = true`. -/
theorem code_morestack {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (h : morestackIn cells = true) : Code exe endPc := by
  simp only [morestackIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨code_field hp hend h0 (by rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]), code_field hp hend h1 rfl, code_field hp hend h2 rfl,
    code_field hp hend h3 rfl, code_field hp hend h4 rfl⟩

end Scc.Cert.Rt.X64.Morestack
