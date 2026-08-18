module

-- This module serves as the root of the `Cpc` library.
-- Import modules here that should be built as part of the library.
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import Cpc.SmtModel
import all Cpc.SmtModel
public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Api
import all Cpc.Api
public import Cpc.ApiChecks
import all Cpc.ApiChecks

-- `Cpc.ApiCorrect` is deliberately not imported here: it depends on
-- `Cpc.Proofs.Checker`, and so on the whole rule-correctness tree, which is too
-- expensive to build as part of the default target.

public section
