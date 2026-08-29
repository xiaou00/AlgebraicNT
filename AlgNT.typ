#import "template.typ": *

#show: doc => conf(
  title: [
    Algebraic Number Theory
  ],
  subtitle: [Some Basics],
  date: "2026",
  cover-image: "cover.png",
  doc,
)

#part[Dedekind Domains]

#include "chapters/chapter_01.typ"

#include "chapters/chapter_02.typ"

#include "chapters/chapter_03.typ"

#include "chapters/chapter_04.typ"

#include "chapters/chapter_05.typ"
