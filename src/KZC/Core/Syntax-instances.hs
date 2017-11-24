instance Located (Decl a) where
  locOf (StructD _ l) = locOf l
  locOf (LetD _ l) = locOf l
  locOf (LetFunD _ _ _ _ _ l) = locOf l
  locOf (LetExtFunD _ _ _ _ l) = locOf l
  locOf (LetCompD _ _ _ l) = locOf l
  locOf (LetFunCompD _ _ _ _ _ l) = locOf l
instance Located (Step a) where
  locOf (VarC _ _ l) = locOf l
  locOf (CallC _ _ _ _ l) = locOf l
  locOf (IfC _ _ _ _ l) = locOf l
  locOf (LetC _ _ l) = locOf l
  locOf (WhileC _ _ _ l) = locOf l
  locOf (ForC _ _ _ _ _ _ l) = locOf l
  locOf (LiftC _ _ l) = locOf l
  locOf (ReturnC _ _ l) = locOf l
  locOf (BindC _ _ _ l) = locOf l
  locOf (TakeC _ _ l) = locOf l
  locOf (TakesC _ _ _ l) = locOf l
  locOf (EmitC _ _ l) = locOf l
  locOf (EmitsC _ _ l) = locOf l
  locOf (RepeatC _ _ _ l) = locOf l
  locOf (ParC _ _ _ _ l) = locOf l
instance Located View where
  locOf (IdxVW _ _ _ l) = locOf l
instance Located LocalDecl where
  locOf (LetLD _ _ _ l) = locOf l
  locOf (LetRefLD _ _ _ l) = locOf l
  locOf (LetTypeLD _ _ _ l) = locOf l
  locOf (LetViewLD _ _ _ l) = locOf l
instance Located Exp where
  locOf (ConstE _ l) = locOf l
  locOf (VarE _ l) = locOf l
  locOf (UnopE _ _ l) = locOf l
  locOf (BinopE _ _ _ l) = locOf l
  locOf (IfE _ _ _ l) = locOf l
  locOf (LetE _ _ l) = locOf l
  locOf (CallE _ _ _ l) = locOf l
  locOf (DerefE _ l) = locOf l
  locOf (AssignE _ _ l) = locOf l
  locOf (LowerE _ l) = locOf l
  locOf (WhileE _ _ l) = locOf l
  locOf (ForE _ _ _ _ _ l) = locOf l
  locOf (ArrayE _ l) = locOf l
  locOf (IdxE _ _ _ l) = locOf l
  locOf (StructE _ _ _ l) = locOf l
  locOf (ProjE _ _ l) = locOf l
  locOf (CastE _ _ l) = locOf l
  locOf (BitcastE _ _ l) = locOf l
  locOf (PrintE _ _ l) = locOf l
  locOf (ErrorE _ _ l) = locOf l
  locOf (ReturnE _ _ l) = locOf l
  locOf (BindE _ _ _ _ l) = locOf l
  locOf (LutE _ _) = NoLoc
  locOf (GenE _ _ l) = locOf l
instance Located Gen where
  locOf (GenG _ _ _ l) = locOf l
  locOf (GenRefG _ _ _ l) = locOf l
