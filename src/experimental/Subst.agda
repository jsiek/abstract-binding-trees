

module experimental.Subst (Op : Set) (sig : Op → List ℕ) where

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; var→val = `_ ; shift = rename (↑ 1)
                    ; var→val-suc-shift = refl
                    ; “_”-0 = refl }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ; g-ext to exts;
    ⧼_⧽ to ⟦_⟧; g-inc to incs; g-drop to drops; g-drop-inc to drops-incs)

