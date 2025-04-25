/* Since `T` in `id` is unbounded, it is invalid in CBQ.
 * Since the bound `Top` in `id` does not exactly match the required
 * bound in `do`, it is not acceptable in Kernel F<:.
 */

Customer = <
  customer : {
    name : String,
    isVIP : Bool
  }
>;

Staff = <
  staff : {
  	name : String
  }
>;

User = <
  customer : {
    name : String,
    isVIP : Bool
  },
  staff : {
    name : String
  }
>;

toStaff = fn T <: User. fn x : T.
  case x as User of
    <customer=c> => <staff={name=c.name}> as User
  | <staff=s> => x as User;

id = fn T <: Top. fn x : T.
  x;

do = fn T <: User. fn f : (All T <: User. T -> User). fn x : T.
  f [T] x;

alice = <
  customer = {
    name = "Alice",
    isVIP = true
  }
> as Customer;

bob = <
  staff = {
    name = "Bob"
  }
> as Staff;

do [Customer] toStaff alice;
do [Customer] id alice;
do [Staff] toStaff bob;
do [Staff] id bob;