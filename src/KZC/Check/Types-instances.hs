instance Located TyVar where
  locOf (TyVar l) = locOf l
instance Located IVar where
  locOf (IVar l) = locOf l
instance Located Type where
  locOf (UnitT l) = locOf l
  locOf (BoolT l) = locOf l
  locOf (BitT l) = locOf l
  locOf (FixT _ _ _ l) = locOf l
  locOf (FloatT _ l) = locOf l
  locOf (StringT l) = locOf l
  locOf (StructT _ l) = locOf l
  locOf (ArrT _ _ l) = locOf l
  locOf (C _ l) = locOf l
  locOf (T l) = locOf l
  locOf (ST _ _ _ _ _ l) = locOf l
  locOf (RefT _ l) = locOf l
  locOf (FunT _ _ _ l) = locOf l
  locOf (ConstI _ l) = locOf l
  locOf (VarI _ l) = locOf l
  locOf (TyVarT _ l) = locOf l
  locOf (MetaT _ l) = locOf l
instance Located StructDef where
  locOf (StructDef _ _ l) = locOf l
