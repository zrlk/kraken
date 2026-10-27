/-
**Private memory never holds a byte of the heap or the static image**
(x64): `Spike/Lib/DmemPriv.lean`'s invariant `PrivInv` on the canonical x64
machine (`machine (kernel n)`), with the ISA's `DomHyps`
(`Scc.Cert.DomX64.domHyps`, fragment `WideSt`: a leaf of Kraken's `exec`
maps exactly the private bytes mapped before).

- `privInv_load`: the invariant at load (`loadProg`), for a `WideSt`
  thread and an entry stack clear of the layout.
- `privInv_step`, `privInv_run`: every step and run keeps it.

The consumer's `hpriv` for thread `t` is then
`((hc.dmemPriv tid t ht).hpriv hwf hE hm hl hk x)` (`PrivKeys.hpriv`).
-/
import Spike.Lib.DmemPriv
import Scc.Cert.Rt.DomX64

namespace Spike.Lib.X64DmemPriv

open Kraken Kraken.Promising Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64 Spike.Lib.DmemPriv

variable {n : Nat} {Λ : Scc.Sem.Layout} {E : Entry} {μ : Marks}

/-- **At load**: thread 0 maps the entry stack, the dormant threads nothing;
every thread `WideSt`; the pool the layout's. -/
theorem privInv_load {cells : List (Directive × Nat)} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hw : WideSt (threadAt E Λ.code.lo cells syms)) (hE : E.clear Λ = true) :
    PrivInv abi WideSt Λ E (loadProg (kernel n) E Λ cells syms mem) := by
  have hfit := (Entry.clear_disjoint hE).1
  refine PrivInv.init_list (I := Kraken.Promising.X64.isa) (K := abi) (Λ := Λ) (Ent := E) (mem_stackMem hfit)
    (fun a => ?_) hw hw ((Entry.clear_disjoint hE).2 _ (by simp [Scc.Sem.Layout.regions]))
  simp [abi, dormantAt]

/-- **Every step keeps the invariant.** -/
theorem privInv_step {tid : Nat} {es : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : PrivInv abi WideSt Λ E c)
    (h : (machine (kernel n)).Step μ tid c es c') : PrivInv abi WideSt Λ E c' :=
  hc.step Scc.Cert.DomX64.domHyps h

/-- **Every run keeps the invariant.** -/
theorem privInv_run {tr : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : PrivInv abi WideSt Λ E c)
    (h : (machine (kernel n)).Run μ c tr c') : PrivInv abi WideSt Λ E c' :=
  hc.run Scc.Cert.DomX64.domHyps h

end Spike.Lib.X64DmemPriv
