structure WithLog (logged : Type) (α : Type) : Type where
  log : List logged
  val : α

def WithLog.pure (val : α) : WithLog logged α := WithLog.mk [] val
def WithLog.bind (result : WithLog logged α) (next : α → WithLog logged β)
: WithLog logged β :=
  let logged := result.log
  let val := result.val
  let result := next val
  let logged := logged ++ result.log
  let val := result.val
  WithLog.mk logged val

instance : Monad (WithLog logged) where
  pure := WithLog.pure
  bind := WithLog.bind
