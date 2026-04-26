/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loren Abdulezer
-/

-- Top-level EML library entry point.
-- Imports the Phase 1 / Phase 2 modules; later phases will be added as they
-- are filled in. Each submodule begins as a placeholder containing only its
-- header and `import Mathlib` (Phase 0); content lands in subsequent phases.
import EML.Syntax
import EML.Denote
import EML.Basic
import EML.Lemma1
import EML.Lemma2
import EML.Lemma3
