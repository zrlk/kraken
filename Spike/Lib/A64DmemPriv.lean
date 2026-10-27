/-
**Private memory never holds a byte of the heap or the static image**
(AArch64): `Spike/Lib/DmemPriv.lean`'s invariant `PrivInv` on the canonical
AArch64 machine (`machine (kernel n)`), with the ISA's `DomHyps`
(`Scc.Cert.DomA64.domHyps`, fragment `WideSt`: a leaf of Kraken's `exec`
maps exactly the private bytes mapped before).

- `privInv_load`: the invariant at load (`loadProg`), for a `WideSt`
  thread and an entry stack clear of the layout.
- `privInv_step`, `privInv_run`: every step and run keeps it.

The consumer's `hpriv` for thread `t` is then
`((hc.dmemPriv tid t ht).hpriv hwf hE hm hl hk x)` (`PrivKeys.hpriv`).
-/
import Spike.Lib.DmemPriv
import Scc.Cert.Rt.DomA64

namespace Spike.Lib.A64DmemPriv

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64 Spike.Lib.DmemPriv

variable {n : Nat} {Λ : Scc.Sem.Layout} {E : Entry} {μ : Marks}

/-- **At load**: thread 0 maps the entry stack, the dormant threads nothing;
every thread `WideSt`; the pool the layout's. -/
theorem privInv_load {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hw : WideSt (threadAt E Λ.code.lo prog syms)) (hE : E.clear Λ = true) :
    PrivInv abi WideSt Λ E (loadProg (kernel n) E Λ prog syms mem) := by
  have hfit := (Entry.clear_disjoint hE).1
  refine PrivInv.init_list (I := Kraken.Promising.AArch64.isaLSE2) (K := abi) (Λ := Λ) (Ent := E)
    (mem_stackMem hfit) (fun a => ?_) hw hw ((Entry.clear_disjoint hE).2 _ (by simp [Scc.Sem.Layout.regions]))
  simp [abi, dormantAt]

/-- **Every step keeps the invariant.** -/
theorem privInv_step {tid : Nat} {es : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : PrivInv abi WideSt Λ E c)
    (h : (machine (kernel n)).Step μ tid c es c') : PrivInv abi WideSt Λ E c' :=
  hc.step Scc.Cert.DomA64.domHyps h

/-- **Every run keeps the invariant.** -/
theorem privInv_run {tr : List Ev} {c c' : (machine (kernel n)).Cfg} (hc : PrivInv abi WideSt Λ E c)
    (h : (machine (kernel n)).Run μ c tr c') : PrivInv abi WideSt Λ E c' :=
  hc.run Scc.Cert.DomA64.domHyps h

end Spike.Lib.A64DmemPriv
