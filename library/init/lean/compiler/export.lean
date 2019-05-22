/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean
@[extern "lean_get_export_name_for"]
constant getExportNameFor (env : @& Environment) (n : @& Name) : Option Name := default _

def isExport (env : Environment) (n : Name) : Bool :=
(getExportNameFor env n).isSome
end Lean
