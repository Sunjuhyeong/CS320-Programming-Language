package cs320

package object proj03 extends Project03 {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)
  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._
    
    case class TypeEnv(
      vars : Map[String, Type] = Map(), 
      typedefine: Map[String, TypeDef] = Map(),
      typescheme: Map[String, (List[String], Type, Boolean)] = Map() 
      )

    def add_vars(tyEnv:TypeEnv, vars:Map[String, Type]):TypeEnv = {
      tyEnv.copy(vars = tyEnv.vars ++ vars)
    }
    def add_tydefine(tyEnv:TypeEnv, tydefine: Map[String, TypeDef]):TypeEnv = {
      tyEnv.copy(typedefine = tyEnv.typedefine ++ tydefine)
    }
    def add_tyscheme(tyEnv:TypeEnv, tyscheme: Map[String, (List[String], Type, Boolean)]):TypeEnv = {
      tyEnv.copy(typescheme = tyEnv.typescheme ++ tyscheme)
    }
    def notype(msg: Any): Nothing = error(s"no type: $msg")
    
    def same(t1:Type, t2:Type): Type = if (t1 == t2) t1 else notype(s"not same: $t1 , $t2") 

    
    //validity
    def is_type_list_valid(ps:List[Type], tyEnv: TypeEnv):List[Type] = ps match{
      case h::t => 
        List(is_type_valid(h, tyEnv)) ::: is_type_list_valid(t, tyEnv) 
      case Nil => Nil
    }
    def is_type_valid(ty: Type, tyEnv: TypeEnv): Type = ty match {
      case AppT(name, targs) => 
        val typelist = is_type_list_valid(targs, tyEnv)
        val tydef = tyEnv.typedefine.getOrElse(name, notype(s"free type1: $name"))
        if (tydef.tparams.size == targs.size) ty 
        else notype(s"wrong arity for AppT: $name")
      case VarT(name) => 
        if (tyEnv.vars.contains(name)) ty 
        else notype(s"free type2: $name")
      case IntT => ty 
      case BooleanT => ty
      case UnitT => ty
      case ArrowT(ps, r) => ArrowT(is_type_list_valid(ps, tyEnv), is_type_valid(r, tyEnv)) 
      }

    def make_Env_in_Fun(tlist:List[Type], nlist:List[String], tyEnv:TypeEnv):TypeEnv = tlist match{
      case h::t => 
        make_Env_in_Fun(t, nlist.tail, add_tyscheme(tyEnv,Map(nlist.head -> (Nil, h, false))))
      case Nil => tyEnv
    }

    def are_types_same_in_App(tlist:List[Type], elist:List[Expr], tyEnv:TypeEnv):Unit = elist match{
      case h::t => 
        if ( tlist.head == is_type_valid(tyCheck(h, tyEnv), tyEnv) ) {
          are_types_same_in_App(tlist.tail, t, tyEnv)
        }
        else notype("wrong arity for app during matching")
      case Nil => None
    }

    //substitute
    def substitute_list(ps:List[Type], tyEnv: TypeEnv):List[Type] = ps match{
      case h::t => 
        List(substitute(h, tyEnv)) ::: substitute_list(t, tyEnv) 
      case Nil => Nil
    }
    def make_Env_in_substitute(tlist:List[Type], nlist:List[String], tyEnv:TypeEnv):TypeEnv = tlist match{
      case h::t => 
        make_Env_in_substitute(t, nlist.tail, add_vars(tyEnv, Map(nlist.head -> h)))
      case Nil => tyEnv
    }
    def substitute(ty: Type, tyEnv:TypeEnv):Type = ty match{
      case AppT(name, targs) => AppT(name, substitute_list(targs, tyEnv))
      case VarT(name) => tyEnv.vars.get(name) match {
          case Some(v) => v
          case None => ty
        }
      case IntT => ty
      case BooleanT => ty
      case UnitT => ty
      case ArrowT(ps, r) => ArrowT(substitute_list(ps, tyEnv), substitute(r, tyEnv))
    }
    
    def find_variant_in_Match(c:Case, variants:List[Variant]):Variant = variants match{
      case h::t => 
        if (c.variant == h.name) h 
        else find_variant_in_Match(c, t)
      case Nil => notype("there is no finded variants")
    }
    //Case case
    def type_check_in_Match(cases:List[Case], variants:List[Variant], variables:List[String], targs:List[Type], tyEnv:TypeEnv):List[Type] = cases match{
      case h::t => 
        if(variables.size == targs.size){
          val variant = find_variant_in_Match(h, variants)
          if (variant.params.size == h.names.size){
            val emptyenv = TypeEnv(Map(), Map(), Map())
            val tlist = variant.params.map{case x  =>  (Nil, substitute(x, make_Env_in_substitute(targs, variables, emptyenv)), false ) }
            val nametoType = h.names zip tlist
            val nenv = add_tyscheme(tyEnv, nametoType.toMap) //List[Tuple] to map
            List(is_type_valid(tyCheck(h.body, nenv), nenv)):::type_check_in_Match(t, variants, variables, targs, tyEnv)
          }
          else notype("wrong arity between variant's ps & case's name during Match")
        }
        else notype("wrong arity between targs & variables during Match")
      case Nil => Nil
    }

    def type_unity_between_Case(tlist:List[Type], ty:Type):Type = tlist match{
      case h::t => if(h == ty) {type_unity_between_Case(t, ty)} else {
      notype("wrong case type")}
      case Nil => ty
    }

    def var_not_in_Env(tparams:List[String], tyEnv:TypeEnv):TypeEnv = tparams match{
      case h::t => if(tyEnv.vars.contains(h)) notype("variable should not in Env") else {
        var_not_in_Env(t, add_vars(tyEnv, Map(h -> VarT(h))))
        }
      case Nil => tyEnv
    }

    def are_recdefs_well(recdefs: List[RecDef], tyEnv:TypeEnv):Int = recdefs match{
      case h::t => h match{
        case Lazy(name, typ, expr) => 
          same(is_type_valid(typ, tyEnv), is_type_valid(tyCheck(expr, tyEnv), tyEnv))
          are_recdefs_well(t, tyEnv)
        case RecFun(name, tparams, params, rtype, body) => 
          val nenv = var_not_in_Env(tparams, tyEnv)
          params.map{case (_,y) => is_type_valid(y, nenv)}
          is_type_valid(rtype, nenv)
          val pmap = params.map{case (x,y) => (x, (Nil, y, false))}
          val nnenv = add_tyscheme(nenv, pmap.toMap)
          is_type_valid(tyCheck(body, nnenv), nnenv)
          are_recdefs_well(t, tyEnv)
        case TypeDef(name, tparams, variants) => 
          val nenv = var_not_in_Env(tparams, tyEnv)
          variants.map{case x => x.params.map{case y => is_type_valid(y, nenv)}}
          are_recdefs_well(t, tyEnv)}
      case Nil => 0
    }

    def make_Env_in_RecBinds(recdefs: List[RecDef], tyEnv:TypeEnv):TypeEnv = recdefs match{
      case h::t => h match {
        case Lazy(name, typ, expr) => 
          val nenv = add_tyscheme(tyEnv, Map(name -> (Nil, typ, false)))
          make_Env_in_RecBinds(t, nenv)
        case RecFun(name, tparams, params, rtype, body) => 
          val nenv = add_tyscheme(tyEnv, Map(name -> (tparams, ArrowT(params.map{case(_,y) => y}, rtype), false)))
          make_Env_in_RecBinds(t, nenv)
        case TypeDef(name, tparams, variants) => 
          val nenv = add_tydefine(tyEnv,  Map(name -> TypeDef(name, tparams, variants)))
          make_Env_in_RecBinds(t, make_variant_Env(name, tparams, variants, nenv))
      }
      case Nil => tyEnv
    }

    def make_variant_Env(name:String, tparams:List[String], variants:List[Variant], tyEnv:TypeEnv):TypeEnv = variants match{
      case h::t =>
        if (h.params.size == 0){
          val nenv = add_tyscheme(tyEnv, Map(h.name -> (tparams, AppT(name, tparams.map(VarT(_))), false))) 
          make_variant_Env(name, tparams, t, nenv)
          }
        else {add_tyscheme(tyEnv, Map(h.name -> (tparams, ArrowT(h.params, AppT(name, tparams.map(VarT(_)))), false)))
          val nenv = add_tyscheme(tyEnv, Map(h.name -> (tparams, ArrowT(h.params, AppT(name, tparams.map(VarT(_)))), false)))
          make_variant_Env(name, tparams, t, nenv)
          }
      case Nil => tyEnv
    }
      def tydef_not_in_Env(defs:List[RecDef], tyEnv:TypeEnv):Int = defs match{
        case h::t => h match {
          case TypeDef(name, _, _) =>
            if (tyEnv.typedefine.contains(name)) notype("should not contain new typedef") 
            else tydef_not_in_Env(t, tyEnv)
          case _ => tydef_not_in_Env(t, tyEnv)
          }
        case Nil => 0
      } 
    
      def tyCheck(expr:Expr, tyEnv:TypeEnv):Type = expr match{
        case Id(name, targs) =>
          val tlist = is_type_list_valid(targs, tyEnv)
          val (variables, rt, mut) = tyEnv.typescheme.getOrElse(name, notype(s"free type3: $name"))
          if (targs.size == variables.size) {
            val nenv = TypeEnv(Map(), Map(), Map())
            is_type_valid(substitute(rt, make_Env_in_substitute(targs, variables, nenv)), tyEnv)
          } 
          else notype(s"wrong arity for Id: $name")
        case IntE(_) => IntT
        case BooleanE(_) => BooleanT
        case UnitE => UnitT
        case Add(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT)
        case Mul(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT) 
        case Div(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT) 
        case Mod(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT)
        case Eq(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT)
          BooleanT
        case Lt(l, r) => 
          same(is_type_valid(tyCheck(l, tyEnv), tyEnv), IntT) 
          same(is_type_valid(tyCheck(r, tyEnv), tyEnv), IntT)
          BooleanT
        case Sequence(l, r) =>
          is_type_valid(tyCheck(l, tyEnv), tyEnv)
          is_type_valid(tyCheck(r, tyEnv), tyEnv)
        case If(c, t, f) => 
          same(is_type_valid(tyCheck(c, tyEnv), tyEnv), BooleanT)
          same(is_type_valid(tyCheck(t, tyEnv), tyEnv), is_type_valid(tyCheck(f, tyEnv), tyEnv))
        case Val(mut, name, typ, expr, body) => typ match{
          case Some(t) => 
            val t1 = is_type_valid(t, tyEnv)
            val t2 = is_type_valid(tyCheck(expr, tyEnv), tyEnv)
            same(t1, t2)
            val nenv = add_tyscheme(tyEnv, Map(name -> (Nil, t2, mut)))
            is_type_valid(tyCheck(body, nenv), nenv)
          case None => 
            val t2 = is_type_valid(tyCheck(expr, tyEnv), tyEnv)
            val nenv = add_tyscheme(tyEnv, Map(name -> (Nil, t2, mut)))
            is_type_valid(tyCheck(body, nenv), nenv)
          }
        case RecBinds(defs, body) => 
          tydef_not_in_Env(defs, tyEnv)
          val nenv = make_Env_in_RecBinds(defs, tyEnv)
          are_recdefs_well(defs, nenv)
          is_type_valid(tyCheck(body, nenv), tyEnv)
        case Fun(ps, body) => 
          val tlist = ps.map{ case(x,y) => y }
          val nlist = ps.map{ case(x,y) => x }
          val targs = is_type_list_valid(tlist, tyEnv)
          val nenv = make_Env_in_Fun(tlist, nlist, tyEnv)
          ArrowT(targs, is_type_valid(tyCheck(body, nenv), nenv))
        case Assign(name, expr) =>
          val (variables, rt, mut) = tyEnv.typescheme.getOrElse(name, notype(s"free type4: $name"))
          if(variables.size == 0) {
            if(mut == true) {
              if (rt == is_type_valid(tyCheck(expr, tyEnv), tyEnv)) {
                UnitT
              }
              else notype("assigning should have same type between rt and expr!")
            }
            else notype("assigning should be var!")
          }
          else notype("assigning should be 0-arg!")
        case App(fun, as) => is_type_valid(tyCheck(fun, tyEnv), tyEnv) match {
          case ArrowT(ps, rt) => 
            if (ps.size == as.size){
              are_types_same_in_App(ps, as, tyEnv)
              rt
            }
            else notype("wrong arity for app")
          case _ => notype("not a function type for app")
        }
        case Match(expr, cases) => 
          val t1 = is_type_valid(tyCheck(expr, tyEnv), tyEnv)
          t1 match{
            case AppT(name, targs) => 
              val tydef = tyEnv.typedefine.getOrElse(name, notype(s"free type5: $name"))
              if (targs.size == tydef.tparams.size){
                if (cases.size == tydef.variants.size){
                  val casetypelist = type_check_in_Match(cases, tydef.variants, tydef.tparams, targs, tyEnv)
                  type_unity_between_Case(casetypelist, casetypelist(0))
                }
                else notype("wrong arity2 during Match")
              }
              else notype("wrong arity between targs & variables during Match")
            case _ => notype("not AppT for Match case")
          }

        }

      def typeCheck(expr: Expr): Type = {
        tyCheck(expr, TypeEnv(Map(),Map(),Map()))
    }
  }

  object U {
    import Untyped._

    type Sto = Map[Addr, Value]

    def Op(op:(Int, Int) => Int) : (Value, Value) => Value = (_, _) match{
    case (IntV(x), IntV(y)) => IntV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
    } 
    def Bop(op:(Int, Int) => Boolean) : (Value, Value) => Value = (_, _) match{
      case (IntV(x), IntV(y)) => BooleanV(op(x, y))
      case (x, y) => error(s"not both integer: $x, $y")
    }

    def malloc(sto: Sto): Addr = maxAddress(sto) + 1
    def maxAddress(sto: Sto): Addr = sto.keySet.+(0).max
    
    def interpret_as(env:Env, sto:Sto, x:List[Expr]): List[(Value, Sto)] = x match {  
      case h::t => 
        val (lv, ls) = interpret(h, env, sto) 
        List((lv, ls)) ::: interpret_as(env, ls, t)
      case Nil => Nil
    }
    def make_Env_Sto_in_App(env:Env, sto:Sto, n:List[String], v:List[(Value, Sto)]): (Env, Sto) = v match{
      case (value, _)::t =>
        val addr = malloc(sto)
        val nenv = env + (n.head -> addr)
        val nsto = sto + (addr -> value)
        make_Env_Sto_in_App(nenv, nsto, n.tail, t)
      case Nil => (env, sto)
    }
    
    def make_Env_in_RecBinds(addr:Addr, fenv:Env, ds:List[RecDef]): Env = ds match{
      case h::t => h match {
        case Lazy(name, expr) => make_Env_in_RecBinds(addr + 1, fenv + (name -> addr), t)
        case RecFun(name, params, body) => make_Env_in_RecBinds(addr + 1, fenv + (name -> addr), t)
        case TypeDef(variants) => 
        val (nenv,naddr) = make_Env_in_RecBinds_for_typedef(addr, variants, Map())
        make_Env_in_RecBinds(naddr + 1, fenv ++ nenv, t)
      }
      case Nil => fenv 
    }
    def make_Env_in_RecBinds_for_typedef(addr:Addr, variants:List[Variant], env:Env):(Env, Addr) = variants match {
      case Variant(name, _ )::tail => 
      make_Env_in_RecBinds_for_typedef(addr+1, tail, env + (name -> addr))
      case Nil => (env, addr)
    }
    def make_Sto_in_RecBinds(env:Env, sto:Sto, ds:List[RecDef]): Sto = ds match{
      case h::t => h match {
        case Lazy(name, expr) => 
          val addr = env.getOrElse(name, error(s"free identifier3: $name"))
          make_Sto_in_RecBinds(env, sto + (addr -> ExprV(expr, env)), t)
        case RecFun(name, params, body) => 
          val addr = env.getOrElse(name, error(s"free identifier4: $name"))
          make_Sto_in_RecBinds(env, sto + (addr -> CloV(params, body, env)), t)
        case TypeDef(variants) => 
          val nsto = make_Sto_in_RecBinds_for_typedef(variants, env, Map())
          make_Sto_in_RecBinds(env, sto ++ nsto, t)     
      }
      case Nil => sto
    }
    def make_Sto_in_RecBinds_for_typedef(variants:List[Variant], env:Env, sto:Sto):Sto = variants match {
      case Variant(name, false)::tail => 
        val addr = env.getOrElse(name, error(s"free identifier1: $name"))
        make_Sto_in_RecBinds_for_typedef(tail, env, sto + (addr -> ConstructorV(name)))
      case Variant(name, true)::tail => 
        val addr = env.getOrElse(name, error(s"free identifier2: $name"))
        make_Sto_in_RecBinds_for_typedef(tail, env, sto + (addr -> VariantV(name, Nil)))
      case Nil => sto
    }

    def find_case(vn:String, cs:List[Case]):(String, List[String], Expr) = cs match{
      case Case(v, names, body)::t => 
        if (vn == v){(v, names, body)}
        else {find_case(vn, t)}
      case Nil => error("There isn't a matched case")
    }
    def make_Env_Sto_in_Case(env:Env, sto:Sto, vl:List[Value], sl:List[String]) :(Env, Sto) = vl match {
      case h::t => 
        val addr = malloc(sto)
        make_Env_Sto_in_Case(env + (sl.head -> addr), sto + (addr -> h), t, sl.tail)
      case Nil => (env, sto)
    }

    
      def interpret(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match {
        case Id(name) =>
          val addr = env.getOrElse(name, error(s"free identifier5: $name"))
          val value = sto.getOrElse(addr, error(s"Not in store: $addr"))
          value match {
            case ExprV(e, nenv) => 
              val (evalue, nsto) = interpret(e, nenv, sto)
              (evalue, nsto + (addr -> evalue))
            case _ => 
            (value, sto)
          }
        case IntE(n) => (IntV(n), sto)
        case BooleanE(b) => (BooleanV(b), sto)
        case UnitE => (UnitV, sto)
        case Add(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls) 
          (Op(_ + _)(lv, rv), rs)
        case Mul(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls) 
          (Op(_ * _)(lv, rv), rs)
        case Div(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls)
          rv match {
            case IntV(0) => error("devide by zero!")
            case _ => (Op(_ / _)(lv, rv), rs)
            }
        case Mod(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls)
          rv match{
            case IntV(0) => error("devide by zero!")
            case _ => (Op(_ % _)(lv, rv), rs)
            }
        case Eq(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls) 
          (Bop(_ == _)(lv, rv), rs)
        case Lt(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          val (rv, rs) = interpret(r, env, ls) 
          (Bop(_ < _)(lv, rv), rs)
        case Sequence(l, r) => 
          val (lv, ls) = interpret(l, env, sto) 
          interpret(r, env, ls)
        case If(c, t, f) => 
          val (cv, cs) = interpret(c, env, sto) 
          cv match {
            case BooleanV(true) => interpret(t, env, cs)
            case BooleanV(false) => interpret(f, env, cs)
            case _ => error("not a boolean for if")
          }
        case Val(n, i, b) => 
          val (iv, is) = interpret(i, env, sto)
          val addr = malloc(is)
          interpret(b, env + (n -> addr), is + (addr -> iv))
        case RecBinds(ds, b) => 
          val addr = malloc(sto)
          val nenv = env ++ make_Env_in_RecBinds(addr, Map(), ds) 
          val nsto = make_Sto_in_RecBinds(nenv, sto, ds) 
          interpret(b, nenv, nsto)
        case Fun(ps, b) => (CloV(ps, b, env), sto)
        case Assign(name, b) => 
          val addr = env.getOrElse(name, error(s"free identifier6: $name"))
          val (bv, bs) = interpret(b, env, sto)
          (UnitV, bs + (addr -> bv))
        case App(f, as) => 
          val (fv, fs) = interpret(f, env, sto) 
          fv match {
            case CloV(ps, e, fenv) =>
              val av:List[(Value, Sto)] = interpret_as(env, fs, as)
              if (av.size == ps.size) {
                if (av.size == 0){
                  interpret(e, fenv, fs)
                } else{
                  val (lv,ls) = av.last
                  val (lenv, lsto) = make_Env_Sto_in_App(fenv, ls, ps, av)
                  interpret(e, lenv, lsto)}
                  } else error("wrong arity")
            case ConstructorV(vn) =>
              val av:List[(Value, Sto)] = interpret_as(env, fs, as)
              if (av.size == 0) {
                (VariantV(vn, Nil), fs)
              } else{
              val (_, fsto) = av.last
              (VariantV(vn, av.map{case (x,_) => x}), fsto)}
            case _ => error(s"not a closure or constructor: $fv") 
          }
        case Match(expr, cases) =>
          val (ev, es) = interpret(expr, env, sto)
          ev match {
            case VariantV(vn, vs) => 
              val (variants, names, body) = find_case(vn, cases)
              if (names.size == vs.size){
                val (nenv, nsto) = make_Env_Sto_in_Case(env, es, vs, names)
                interpret(body, nenv, nsto)
              }
              else{error("wrong arity for match")}
            case _ => error("not a variants for Match")
          }
      }
      def interp(expr: Expr): Value = {
      val (answer, _) = interpret(expr, Map[String, Addr](), Map[Addr, Value]())
      answer
    }
  }

  def tests: Unit = {
    // test-interpret
    test(run("42"), "42")
    // test-boolean
    test(run("true"), "true")
    // test-unit
    test(run("()"), "()")

    // test-add
    test(run("1 + 2"), "3")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-eq
    test(run("1 == 1"), "true")
    // test-lt
    test(run("1 < 1"), "false")
    // test-seq
    test(run("{1; 2}"), "2")

    // test-if
    test(run("if (true) 1 else 2"), "1")

    // test-val
    test(run("""
      val x = 1 + 2;
      val y: Int = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-lazy
    test(run("""
      lazy val f: Int => Int = (x: Int) => if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")
    // test-rec
    test(run("""
      def f(x: Int): Int = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")

    // test-fun
    test(run("(x: Int) => x + x"), "<function>")
    // test-app
    test(run("((x: Int, y: Int) => x + y)(1, 2)"), "3")

    // test-var-assign
    test(run("""
      var x = 1;
      var y: Int = x * 4 + 8;
      { x = 3; y / (x - 1) }
    """), "6")

    // test-type-match
    test(run("""
      type Fruit {
        case Apple
        case Banana(Int)
      }
      (Apple match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana(1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-poly1
    test(run("""
      def f['T, 'S](t: 'T, s: 'S): 'T = t;
      f[Int, Boolean](1, true)
    """), "1")
    // test-poly2
    test(run("""
      type Fruit['T] {
        case Apple
        case Banana('T)
      }
      (Apple[Boolean] match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana[Int](1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-primitive
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(!intEquals(1, 2));
check(intEquals(3, 3));
check(intMax(3, 6) == 6);
check(intMin(3, 6) == 3);
check(!booleanEquals(true, false));
check(booleanEquals(true, true));
check(unitEquals((), ()));

score
}"""
      ),
      "7"
    )

    // test-pair
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val p1 = Pair[Int, Boolean](1, true);
val p2 = Pair[Int, Boolean](1, false);
val p3 = Pair[Int, Boolean](2, true);

val eq = pairEquals[Int, Boolean](intEquals, booleanEquals);

{
check(pairFst[Int, Boolean](p1) == 1);
check(pairSnd[Int, Boolean](p1));
check(pairFst[Int, Boolean](p2) == 1);
check(!pairSnd[Int, Boolean](p2));
check(pairFst[Int, Boolean](p3) == 2);
check(pairSnd[Int, Boolean](p3));
check(eq(p1, p1));
check(!eq(p1, p2));
check(!eq(p1, p3));

score
}"""
      ),
      "9"
    )

    // test-option
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val opt1 = Some[Int](1);
val opt2 = optionMap[Int, Int](opt1, (x: Int) => x + x);
val opt3 = optionFilter[Int](opt1, (x: Int) => x < 2);
val opt4 = optionFilter[Int](opt2, (x: Int) => x < 2);
val opt5 = optionFlatten[Int](Some[Option[Int]](opt1));
val opt6 = optionFlatten[Int](Some[Option[Int]](opt4));
val opt7 = optionFlatten[Int](None[Option[Int]]);

def aux(i: Int): Option[Int] =
  if (i == 1) Some[Int](i) else None[Int];

val opt8 = optionFlatMap[Int, Int](opt1, aux);
val opt9 = optionFlatMap[Int, Int](opt2, aux);
val opt10 = optionFlatMap[Int, Int](opt4, aux);
val opt11 = optionFilterNot[Int](opt1, (x: Int) => x < 2);
val opt12 = optionFilterNot[Int](opt2, (x: Int) => x < 2);

val eq = optionEquals[Int](intEquals);
val eql = listEquals[Int](intEquals);

{
check(eq(Some[Int](1), Some[Int](1)));
check(!eq(Some[Int](1), Some[Int](2)));
check(!eq(Some[Int](1), None[Int]));
check(eq(None[Int], None[Int]));
check(eq(opt1, Some[Int](1)));
check(eq(opt2, Some[Int](2)));
check(eq(opt3, Some[Int](1)));
check(eq(opt4, None[Int]));
check(eq(opt5, Some[Int](1)));
check(eq(opt6, None[Int]));
check(eq(opt7, None[Int]));
check(eq(opt8, Some[Int](1)));
check(eq(opt9, None[Int]));
check(eq(opt10, None[Int]));
check(eq(opt11, None[Int]));
check(eq(opt12, Some[Int](2)));
check(!optionIsEmpty[Int](opt1));
check(optionIsEmpty[Int](opt4));
check(optionNonEmpty[Int](opt1));
check(!optionNonEmpty[Int](opt4));
check(eql(optionToList[Int](opt1), List1[Int](1)));
check(eql(optionToList[Int](opt4), List0[Int]()));
check(optionGetOrElse[Int](opt1, 0) == 1);
check(optionGetOrElse[Int](opt4, 0) == 0);
optionForeach[Int](opt1, (i: Int) => check(i == 1));
optionForeach[Int](opt4, (i: Int) => check(true));

score
}"""
      ),
      "25"
    )

    // test-box
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val b = Box[Int](1);
val i1 = boxGet[Int](b);
val i2 = boxSet[Int](b, 2);
val i3 = boxGet[Int](b);
val i4 = boxSet[Int](b, 1);
val i5 = boxGet[Int](b);

{
check(i1 == 1);
check(i2 == 1);
check(i3 == 2);
check(i4 == 2);
check(i5 == 1);

score
}"""
      ),
      "5"
    )

    // test-list
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val l0 = List5[Int](1, 2, 3, 4, 5);
val l1 = List3[Int](1, 2, 3);
val l2 = List2[Int](4, 5);
val zipped0 = listZip[Int, Int](l0, l0);
val unzipped0 = listUnzip[Int, Int](zipped0);
val l3 = pairFst[List[Int], List[Int]](unzipped0);
val l4 = pairSnd[List[Int], List[Int]](unzipped0);
val zipped1 = listZip[Int, Int](l0, l1);
val unzipped1 = listUnzip[Int, Int](zipped1);
val l5 = pairFst[List[Int], List[Int]](unzipped1);
val l6 = pairSnd[List[Int], List[Int]](unzipped1);
val zipped2 = listZipWithIndex[Int](l0);
val unzipped2 = listUnzip[Int, Int](zipped2);
val l7 = pairFst[List[Int], List[Int]](unzipped2);
val l8 = pairSnd[List[Int], List[Int]](unzipped2);

val eq = listEquals[Int](intEquals);
val eqo = optionEquals[Int](intEquals);
def odd(n: Int): Boolean = n % 2 != 0;
def lt4(n: Int): Boolean = n < 4;

{
check(eq(l0, l0));
check(!eq(l0, l1));
check(!eq(l0, l2));
check(!eq(l1, l2));
check(!eq(l0, Nil[Int]));
check(eq(Nil[Int], Nil[Int]));
check(eq(listAppended[Int](listAppended[Int](l1, 4), 5), l0));
check(eq(listConcat[Int](l1, l2), l0));
check(listCount[Int](l0, odd) == 3);
check(eq(listDrop[Int](l0, 3), l2));
check(listExists[Int](l0, lt4));
check(!listExists[Int](l2, lt4));
check(eq(listFilter[Int](l0, lt4), l1));
check(eq(listFilterNot[Int](l0, lt4), l2));
check(eqo(listFind[Int](l0, lt4), Some[Int](1)));
check(eqo(listFind[Int](l2, lt4), None[Int]));
check(eq(listFlatMap[Int, Int](l1, (n: Int) => if (n == 1) l1 else if (n == 2) l2 else Nil[Int]), l0));
check(eq(listFlatten[Int](List2[List[Int]](l1, l2)), l0));
check(listFoldLeft[Int, Int](0, l0, (n: Int, m: Int) => n + m) == 15);
check(listFoldRight[Int, Int](l0, 0, (n: Int, m: Int) => n + m) == 15);
check(!listForall[Int](l0, lt4));
check(listForall[Int](l1, lt4));
listForeach[Int](l0, (n: Int) => check(odd(n)));
check(eqo(listGet[Int](l0, 4), Some[Int](5)));
check(eqo(listGet[Int](l0, 5), None[Int]));
check(!listIsEmpty[Int](l0));
check(listIsEmpty[Int](Nil[Int]));
check(listLength[Int](l0) == 5);
check(eq(listMap[Int, Int](l0, (n: Int) => n * n), List5[Int](1, 4, 9, 16, 25)));
check(listNonEmpty[Int](l0));
check(!listNonEmpty[Int](Nil[Int]));
check(eq(listPrepended[Int](listPrepended[Int](listPrepended[Int](l2, 3), 2), 1), l0));
check(eq(listReverse[Int](l0), List5[Int](5, 4, 3, 2, 1)));
check(eq(listTake[Int](l0, 3), l1));
check(eq(l0, l3));
check(eq(l0, l4));
check(eq(l1, l5));
check(eq(l1, l6));
check(eq(l0, l7));
check(eq(l0, listMap[Int, Int](l8, (n: Int) => n + 1)));

score
}"""
      ),
      "42"
    )

    // test-map
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val m0 = Map1[Int, Int](intEquals, 0, 0);
val m1 = mapUpdated[Int, Int](m0, 1, 2);
val m2 = mapUpdated[Int, Int](m1, 2, 4);
val m3 = mapUpdated[Int, Int](m2, 3, 6);
val m4 = mapRemoved[Int, Int](m3, 2);
val m5 = mapUpdated[Int, Int](m2, 3, 8);

val eqo = optionEquals[Int](intEquals);

{
check(eqo(mapGet[Int, Int](m0, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m0, 1), None[Int]));
check(eqo(mapGet[Int, Int](m0, 2), None[Int]));
check(eqo(mapGet[Int, Int](m0, 3), None[Int]));
check(eqo(mapGet[Int, Int](m0, 4), None[Int]));

check(eqo(mapGet[Int, Int](m1, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m1, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m1, 2), None[Int]));
check(eqo(mapGet[Int, Int](m1, 3), None[Int]));
check(eqo(mapGet[Int, Int](m1, 4), None[Int]));

check(eqo(mapGet[Int, Int](m2, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m2, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m2, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m2, 3), None[Int]));
check(eqo(mapGet[Int, Int](m2, 4), None[Int]));

check(eqo(mapGet[Int, Int](m3, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m3, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m3, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m3, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m3, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

score
}"""
      ),
      "30"
    )

    // test-string
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(stringEquals("abc \n"<STRP, EOS>, List5[Int](97, 98, 99, 32, 10)));
check(stringEquals(substring("12abc \n"<STRP, EOS>, 2, 5), List3[Int](97, 98, 99)));
check("abc \n"<(n: Int, m: Int) => n + m, 0> == 336);

score
}"""
      ),
      "3"
    )

    // test-fae
    test(
      runWithStdLib(
"""
type Expr {
  case Num(Int)
  case Add(Expr, Expr)
  case Sub(Expr, Expr)
  case Id(Int)
  case Fun(Int, Expr)
  case App(Expr, Expr)
}

type Value {
  case NumV(Int)
  case CloV(Int, Expr, Map[Int, Value])
}

def interp(e: Expr, env: Map[Int, Value]): Option[Value] = e match {
  case Num(n) => Some[Value](NumV(n))
  case Add(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n + m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Sub(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n - m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Id(x) => mapGet[Int, Value](env, x)
  case Fun(x, e) => Some[Value](CloV(x, e, env))
  case App(f, a) => optionFlatMap[Value, Value](interp(f, env), (fv: Value) => fv match {
    case NumV(n) => None[Value]
    case CloV(x, e, fenv) => optionFlatMap[Value, Value](interp(a, env),
      (av: Value) => interp(e, mapUpdated[Int, Value](fenv, x, av))
    )
  })
};

lazy val digit: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 48 <= x && x < 58),
    (x: Int) => Num(x - 48)
  );

lazy val add: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(43),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Add(l, r)
      }
  );

lazy val sub: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(45),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Sub(l, r)
      }
  );

lazy val id: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 97 <= x && x <= 122),
    (x: Int) => Id(x)
  );

lazy val fun: Parser[Expr] =
  parserMap[Pair[Int, Pair[Int, Expr]], Expr](
    () => parserThen[Int, Pair[Int, Expr]](
      () => parserConst(47),
      () => parserThen[Int, Expr](
        () => parserCond((x: Int) => 97 <= x && x <= 122),
        () => e
      )
    ),
    (p: Pair[Int, Pair[Int, Expr]]) =>
      pairSnd[Int, Pair[Int, Expr]](p) match {
        case Pair(p, b) => Fun(p, b)
      }
  );

lazy val app: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(64),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => App(l, r)
      }
  );

lazy val e: Parser[Expr] =
  parserOr[Expr](
    () => parserOr[Expr](
      () => parserOr[Expr](
        () => parserOr[Expr](
          () => parserOr[Expr](
            () => digit,
            () => add
          ),
          () => sub
        ),
        () => id
      ),
      () => fun
    ),
    () => app
  );

parseAll[Expr](e, "@@/x/y+xy23"<STRP, EOS>) match {
  case None => -1
  case Some(e) => interp(e, Map0[Int, Value](intEquals)) match {
    case None => -2
    case Some(v) => v match {
      case NumV(n) => if (n < 0) -3 else n
      case CloV(x, e, env) => -4
    }
  }
}
"""
      ),
      "5"
    )
  }

}
