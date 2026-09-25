/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Syntax
public import Complexity.Control.Program.Compiler

/-! # Programs with finite control

Programs are syntax over a fixed operation signature. Their native control types are generated
by compilation, so composition stores neither arbitrary types nor numbered control graphs.
Only imported finite controllers use a supplied finite numbering at their boundary.
-/
