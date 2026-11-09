import Scc.Cert.MapsLeast
import Scc.Cert.MapsEmitA64

/-!
# The AArch64 tables' stage from a ranked witness is the reference stage (untrusted)

`emitTablesW` (`Scc.Cert.MapsEmitA64`) builds the GC tables from a ranked liveness witness, refusing unless
every witness is its function's least fixpoint (`computeWR`). By
`Scc.Cert.Maps.compute_of_computeWR` the tables it accepts are `compute`'s, so whatever
`emitTablesW` returns is `emitTables`' result (`emitTables_of_emitTablesW`): a certificate that
checks the stage with a witness checks the reference stage.
-/

namespace Scc.Cert.MapsA64
open Maps

/-- **What `emitTablesW` returns is `emitTables`' result**, whatever the witness. -/
theorem emitTables_of_emitTablesW {p : IR.Program} {its : List Scc.Emit.A64.Item} {gw : GcWit}
    {d : DescLabels} {r : List Scc.Emit.A64.Item × List DItem}
    (h : emitTablesW p its gw d = .ok r) : emitTables p its d = .ok r := by
  unfold emitTablesW at h
  unfold emitTables emitTablesWith computeA64
  cases hg : p.growth.isNone
  · simp only [hg, Bool.false_eq_true, ite_false] at h ⊢
    unfold fnTagsA64 at h
    cases ha : Scc.Emit.A64.emitPre p with
    | error e => simp [ha, bind, Except.bind] at h
    | ok areas =>
      cases hi : itemsOf its with
      | error e => simp [ha, hi, bind, Except.bind] at h
      | ok items =>
        cases ht : stackTable its items with
        | error e => simp [ha, hi, ht, bind, Except.bind] at h
        | ok stbl =>
          cases hf : p.funcs.zipIdx.mapM (tagsOf p areas items stbl) with
          | error e => simp [ha, hi, ht, hf, bind, Except.bind] at h
          | ok fns =>
            cases hc : computeWR fns items gw with
            | error e => simp [ha, hi, ht, hf, hc, bind, Except.bind, pure, Except.pure] at h
            | ok t =>
              have hc' := compute_of_computeWR hc
              simp only [ha, hi, ht, hf, hc, bind, Except.bind, pure, Except.pure] at h
              simp only [ht, hf, hc', bind, Except.bind, pure, Except.pure]
              exact h
  · simp [hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end Scc.Cert.MapsA64
