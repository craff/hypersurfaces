type 'a previous

(** [create n] create a queue of at most [n] elements. *)
val create : int -> 'a previous

(** [add x q] add [x] to the queue [q]. If [q] would
    have more that [n] elements, then the oldest added
    element is automatically removed *)
val add : 'a -> 'a previous -> unit

(** [get ~pos:n q] returns the nth element of the queue.
    [get ~pos:0 q] means the latest added element.
    [get ~pos:1 q] means the element before [].
    ...
    [get ~pos:(-1) q] (the default) means the oldest element in the queue.
    [n] is taken module the maximum size of the queue.

    [get ~pos q] may raise Not_found if the requested element do not exists in
    then queue. *)
val get : ?pos:int -> 'a previous -> 'a

(** [max_size q] returns maximum number of elements in the queue *)
val max_size : 'a previous -> int

(** [size q] returns the current number of elements in the queue (log time
    in [max_size q], as the current size if not stored *)
val size : 'a previous -> int
