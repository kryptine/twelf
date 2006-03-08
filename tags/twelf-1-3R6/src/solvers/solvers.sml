structure CSManager = CSManager (structure Global = Global
                                 structure IntSyn = IntSyn
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);

structure CSEqQ = CSEqField (structure Field = Rationals
                             structure IntSyn = IntSyn
                             structure Whnf = Whnf
                             structure Unify = UnifyTrail
                             structure CSManager = CSManager);

structure CSIneqQ = CSIneqField (structure OrderedField = Rationals
                                  structure IntSyn = IntSyn
                                  structure Trail = Trail
                                  structure Unify = UnifyTrail
                                  structure SparseArray = SparseArray
                                  structure SparseArray2 = SparseArray2
                                  structure CSManager = CSManager
                                  structure CSEqField = CSEqQ);

structure CSEqStrings = CSEqStrings (structure IntSyn = IntSyn
                                     structure Whnf = Whnf
                                     structure Unify = UnifyTrail
                                     structure CSManager = CSManager);

structure CSEqBools = CSEqBools (structure IntSyn = IntSyn
                                 structure Whnf = Whnf
                                 structure Unify = UnifyTrail
                                 structure CSManager = CSManager);

structure CSEqZ = CSEqIntegers (structure Integers = Integers
                                structure IntSyn = IntSyn
                                structure Whnf = Whnf
                                structure Unify = UnifyTrail
                                structure CSManager = CSManager);

structure CSIneqZ = CSIneqIntegers (structure Integers = Integers
                                    structure Rationals = Rationals
                                    structure IntSyn = IntSyn
                                    structure Trail = Trail
                                    structure Unify = UnifyTrail
                                    structure SparseArray = SparseArray
                                    structure SparseArray2 = SparseArray2
                                    structure CSManager = CSManager
                                    structure CSEqIntegers = CSEqZ);

structure CSIntWord32 = CSIntWord (structure IntSyn = IntSyn
                                   structure Whnf = Whnf
                                   structure Unify = UnifyTrail
                                   structure CSManager = CSManager
                                   val wordSize = 32);

CSManager.installSolver (CSEqQ.solver);
CSManager.installSolver (CSIneqQ.solver);
CSManager.installSolver (CSEqStrings.solver);
CSManager.installSolver (CSEqBools.solver);
CSManager.installSolver (CSEqZ.solver);
CSManager.installSolver (CSIneqZ.solver);
CSManager.installSolver (CSIntWord32.solver);