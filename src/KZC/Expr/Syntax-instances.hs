instance Located Var where
  locOf (Var l) = locOf l
instance Located Field where
  locOf (Field l) = locOf l
instance Located Struct where
  locOf (Struct l) = locOf l
instance Located TyVar where
  locOf (TyVar l) = locOf l
instance Located Decl where
  locOf (StructD _ _ _ l) = locOf l
  locOf (LetD _ _ _ l) = locOf l
  locOf (LetRefD _ _ _ l) = locOf l
  locOf (LetFunD _ _ _ _ _ l) = locOf l
  locOf (LetExtFunD _ _ _ _ l) = locOf l
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
  locOf (TakeE _ l) = locOf l
  locOf (TakesE _ _ l) = locOf l
  locOf (EmitE _ l) = locOf l
  locOf (EmitsE _ l) = locOf l
  locOf (RepeatE _ _ l) = locOf l
  locOf (ParE _ _ _ _ l) = locOf l
instance Located (GenInterval a) where
  locOf (FromToInclusive _ _ l) = locOf l
  locOf (FromToExclusive _ _ l) = locOf l
  locOf (StartLen _ _ l) = locOf l
instance Located StructDef where
  locOf (StructDef _ _ _ l) = locOf l
instance Located Type where
  locOf (UnitT l) = locOf l
  locOf (BoolT l) = locOf l
  locOf (IntT _ l) = locOf l
  locOf (FixT _ l) = locOf l
  locOf (FloatT _ l) = locOf l
  locOf (StringT l) = locOf l
  locOf (StructT _ _ l) = locOf l
  locOf (ArrT _ _ l) = locOf l
  locOf (ST _ _ _ _ l) = locOf l
  locOf (RefT _ l) = locOf l
  locOf (FunT _ _ l) = locOf l
  locOf (NatT _ l) = locOf l
  locOf (ForallT _ _ l) = locOf l
  locOf (TyVarT _ l) = locOf l
instance Located Omega where
  locOf (C _) = NoLoc
  locOf T = NoLoc
