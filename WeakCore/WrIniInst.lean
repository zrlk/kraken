import WeakCore.WLayer
/-! The `WrIniCB` instance, from the generated ♭ port of
TermAnch.wrSite_ok / TermWrSiteA.wrSiteA_okU (WLayer.lean). -/
namespace TermWrSiteA.Flat
open TermTyped.Flat

/-- **`WrIniCB` holds** (both fields). -/
theorem wrIniCB : WrIniCB :=
  ⟨fun hE hT htv hi hm hsc hr => TermAnch.Flat.wrSite_okB hE hT htv hi hm hsc hr,
   fun hE hT htv hi hm hsc hvr hr => wrSiteA_okUB hE hT htv hi hm hsc hvr hr⟩

instance : WrIniCB := wrIniCB
end TermWrSiteA.Flat
