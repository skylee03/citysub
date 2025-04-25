/* Subsective adjectives in natural languages can be modelled as generic functions.
 * However, we should exclude phrases like 'skilful building'.
 * This can be done with bounded quantification.
 */

CN = {};
Human <: CN;
Building <: CN;
Actor <: Human;

Prop <: Top;

small : All T <: CN. T -> Prop;
skilful : All T <: Human. T -> Prop;

cpd : Building;
jackieChan : Actor;

small [Actor] jackieChan;
small [Building] cpd;
skilful [Actor] jackieChan;
skilful [Building] cpd;

/* The following use of `modify` is invalid in Kernel F<: but valid in others. */
modify = fn T <: CN. fn p : (All S <: T. S -> Prop). fn n : T.
  p [T] n;
modify [Actor] small jackieChan;