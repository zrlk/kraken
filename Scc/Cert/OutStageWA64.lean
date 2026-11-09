import Scc.Lower.SpecA64
import Scc.Cert.MapsLeastA64

/-!
# scc's AArch64 run and a certificate's run with a ranked witness agree (untrusted)

A certificate runs the pipeline with a ranked liveness witness (`Scc.Config.gcWit := some gw`;
the tables' stage `emitTablesW`), scc with none (the reference stage `emitTables`). The
lowering ignores `gcWit` (`lowerIR` is the same function of the rest of the configuration), and
whatever `emitTablesW` gives is `emitTables`' result (`Scc.Cert.MapsA64.emitTables_of_emitTablesW`,
for any witness). So where the certificate's tables' stage succeeds, the two runs are the same
`Emitted`, its sections and tables included (`lowerAll_gcWit_eq`, `lowerAll_eq_of_tables`). The
x64 twin: `Scc.Cert.OutStageWX64`.
-/

namespace Scc.Cert.OutStageWA64
open Scc.Lower.A64

/-- **With the certificate's tables' stage succeeding, scc's run is the certificate's**: the
pipeline at `cfg` with no witness and with the witness `gw` give the same output. -/
theorem lowerAll_gcWit_eq (cfg : Config) (p : CoreTerm.Prog) (gw : List (Array (List Int) × List (List Nat)))
    {r : List Scc.Emit.A64.Item × List Kraken.DataImage.Item}
    (h : (lowerAll { cfg with gcWit := some gw } p).tables = .ok r) :
    lowerAll { cfg with gcWit := none } p = lowerAll { cfg with gcWit := some gw } p := by
  unfold lowerAll lowerAll? at *
  have hI : ∀ x, Lower.lowerIR { cfg with gcWit := x } p = Lower.lowerIR cfg p := fun _ => rfl
  rw [hI (some gw)] at h ⊢
  rw [hI none]
  cases hl : Lower.lowerIR cfg p with
  | error e => simp [hl, bind, Except.bind] at h
  | ok l =>
    simp only [hl, bind, Except.bind] at h ⊢
    unfold emitAll at *
    cases he : Scc.Emit.A64.emitItemsMaps l.ir with
    | error e => simp [he, bind, Except.bind] at h
    | ok v =>
      obtain ⟨items, sps⟩ := v
      simp only [he, bind, Except.bind, pure, Except.pure] at h ⊢
      have ht : tablesOf l.ir items none = tablesOf l.ir items (some gw) := by
        simp only [tablesOf] at h ⊢
        rw [h]; exact Scc.Cert.MapsA64.emitTables_of_emitTablesW h
      rw [ht]

/-- **`lowerAll_gcWit_eq` at scc's configuration** `cfg` (no witness, `cfg.gcWit = none`): the
certificate's configuration is `{ cfg with gcWit := some gw }`. -/
theorem lowerAll_eq_of_tables {cfg : Config} (h0 : cfg.gcWit = none) (p : CoreTerm.Prog)
    (gw : List (Array (List Int) × List (List Nat))) {r : List Scc.Emit.A64.Item × List Kraken.DataImage.Item}
    (h : (lowerAll { cfg with gcWit := some gw } p).tables = .ok r) :
    lowerAll cfg p = lowerAll { cfg with gcWit := some gw } p := by
  have hc : { cfg with gcWit := none } = cfg := by cases cfg; cases h0; rfl
  rw [← lowerAll_gcWit_eq cfg p gw h, hc]

end Scc.Cert.OutStageWA64
