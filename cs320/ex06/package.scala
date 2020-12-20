package cs320

package object ex06 extends Exercise06 {

  def Op(op:(Int, Int) => Int) : (Value, Value) => Value =
  (_, _) match{
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  } 

  def malloc(sto: Sto): Addr = maxAddress(sto) + 1
  def maxAddress(sto: Sto): Addr = sto.keySet.+(0).max


  def interp(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match {
    case Num(n) => (NumV(n), sto)
    case Add(l, r) => 
      val (lv, ls) = interp(l, env, sto) 
      val (rv, rs) = interp(r, env, ls) 
      (Op(_ + _)(lv, rv), rs)
    case Sub(l, r) => 
      val (lv, ls) = interp(l, env, sto) 
      val (rv, rs) = interp(r, env, ls) 
      (Op(_ - _)(lv, rv), rs)
    case Id(x) => (env.getOrElse(x, error(s"free identifier: $x")), sto)
    case Fun(x, e) => (CloV(x, e, env), sto)
    case App(f, a) => interp(f, env, sto) match {
      case (CloV(x, e, fenv), s) => {
        val (lv, ls) = interp(a, env, s)
        interp(e, fenv + (x -> lv), ls)}
      case (v, _) => error(s"not a closure: $v") 
      }
    case NewBox(e) =>
      val (v, s) = interp(e, env, sto)
      val addr = malloc(s)
      (BoxV(addr), s + (addr -> v))
    case SetBox(b, e) => 
      val (bv, bs) = interp(b, env, sto)
      val BoxV(addr) = cast[BoxV](bv, s"not a box: $bv")
      val (ev, es) = interp(e, env, bs)
      (ev, es + (addr -> ev)) 
    case OpenBox(b) => interp(b, env, sto) match {
      case (BoxV(addr), s) => {
        (s.getOrElse(addr, error(s"not in the store: $addr")), s)
      }
      case (v, _) => error(s"not a box: $v")
    }
    case Seqn(l, r) => r.foldLeft(interp(l, env, sto)){case ((v0, s0), e) => interp(e, env, s0)}
    case Rec(f) => 
      val (nfield, s) = f.foldLeft(Map[String, Addr](), sto){
        case ((m0, s0), (f, e)) => {
          val (v, s1) = interp(e, env, s0)
          val addr = malloc(s1)
          (m0 + (f->addr), s1 + (addr->v))
          }
        }
      (RecV(nfield), s)
    case Get(r, f) => {
      val (rv, rs) = interp(r, env, sto)
      val RecV(fields) = cast[RecV](rv, s"not a record: $rv")
      val addr = fields.getOrElse(f, error(s"no such field: $f"))
      val v = rs.getOrElse(addr, error(s"unallocated address: $addr"))
      (v, rs)
    }
    case Set(r, f, e) => {
      val (rv, rs) = interp(r, env, sto)
      val RecV(fields) = cast[RecV](rv, s"not a record: $rv")
      val addr = fields.getOrElse(f, error(s"no such field: $f"))
      val (ev, es) = interp(e, env, rs)
      (ev, es + (addr -> ev))
    }
    
  }

  def tests: Unit = {
    test(run("""{
                  b => {
                    b.set((2 + b.get));
                    b.set((3 + b.get));
                    b.set((4 + b.get));
                    b.get
                  }
                }(Box(1))"""), "10")
    testExc(run("{ x = 1 }.y"), "no such field")
    test(run("""{
                  r => {
                    { r.x = 5 };
                    r.x
                  }
                }({ x = 1 })"""), "5")
    test(run("42"), "42")
    test(run("{ x => x }"), "function")
    test(run("Box(1)"), "box")
    test(run("{}"), "record")

    /* Write your own tests */
  }

  def test2: Unit = {
    test(run("{ 1; 2 }"), "2")
    test(run("{ b => b.get }(Box(10))"), "10")
    test(run("{ b => { b.set(12); b.get } }(Box(10))"), "12")
    test(run("{ b => b.get }({ Box(9); Box(10) })"), "10")
    test(run("{ b => { a => b.get } }(Box(9))(Box(10))"), "9")
    test(run("{ b => { b.set(2); b.get } }(Box(1))"), "2")
    test(run("{ b => { b.set((9 + b.get)); b.get } }(Box(1))"), "10")
    test(run("{ b => { b.set((2 + b.get)); b.set((3 + b.get)); b.set((4 + b.get)); b.get } }(Box(1))"), "10")
    test(run("{ r => r.x }({ x = 1 })"), "1")
    test(run("{ r => { { r.x = 5 }; r.x } }({ x = 1 })"), "5")
    test(run("{ g => { s => { r1 => { r2 => (r1.b + { s(r1)(g(r2)); ({ s(r2)(g(r1)); r1.b } + r2.b) }) } } } }({ r => r.a })({ r => { v => { r.b = v } } })({ a = 0, b = 2 })({ a = 3, b = 4 })"), "5")
    test(run("{ x => x }"), "function")
    test(run("Box(1)"), "box")
    test(run("{}"), "record")
  }
  def test3: Unit = {
    test(run("Box(10).set(2)"), "2")
  }

}