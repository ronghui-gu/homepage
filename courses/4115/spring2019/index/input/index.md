
<img style="float:right; margin: -5px -100px 0px -100px;" src="https://www.laurenillumination.com/wp-content/uploads/2017/10/logo-columbia.png" width="180" height="90">

# COMS W4115 Programming Languages and Translators

### Spring 2019



## General Information

Instructor: [Prof. Ronghui Gu](https://www.cs.columbia.edu/~rgu/)  
Lectures: Mudd 833, Mon & Wed, 2:40pm ~ 3:55pm  

**Staff**  

| Name      | Email | Office hours | Location |  
| ----------- | ----------- |  ----------- |  ----------- |
| Prof. Ronghui Gu |  ronghui.gu@columbia.edu | Th (1-2) | 515 CSB |
| Justin Wong (**lead**)| jw3354@columbia.edu | M (7-8) & T (2-3) | 486 CSB ([Clic Lab](https://www.cs.columbia.edu/clic/)) |  
| Ryan Bernstein (**lead**)| rb3234@columbia.edu | W & F (11-12) | 486 CSB ([Clic Lab](https://www.cs.columbia.edu/clic/)) |  
| Lauren Bree Arnett | lba2138@columbia.edu | Th (3-4) | 486 CSB ([Clic Lab](https://www.cs.columbia.edu/clic/)) |  

**Note**: For any general questions related to assignments and projects,
please send emails to the following
TA mailing list using your Columbia email address:

4115spring2019ta@lists.cs.columbia.edu

### Overview
The goal of PLT is to teach you both about the structure of computer programming languages and the basics of implementing compilers for such languages.

The course will focus mostly on traditional imperative and object-oriented languages, but will also cover functional and logic programming, concurrency issues, and some aspects of scripting languages. Homework and tests will cover language issues. You will design and implement a language of your own design in a semester-long team project.

While few of you will ever implement a full commercial compiler professionally, the concepts, techniques, and tools you will learn have broad application.

### Prerequisites
**COMS W3157 Advanced Programming**: You will be dividing into teams to build a compiler, so you need to have some idea how to keep this under control. *Quick test*: you need to know about Makefiles and source code control systems.

**COMS W3261 Computability and Models of Computation**: You will need an understanding of formal languages and grammar to build the parser and lexical analyzer. *Quick test*: you must know about regular expressions, context-free grammars, and NFAs.

### Suggested Text
You don't need to buy textbooks since all the materials will be covered by the lecture notes.
- [Compilers: Principles, Techniques, and Tools](https://www.amazon.com/Compilers-Principles-Techniques-Tools-2nd/dp/0321486811)
 by Alfred V. Aho, Monica Lam, Ravi Sethi, and Jeffrey D. Ullman (Second Edition).

- [Modern Compiler Implementation in ML](http://www.cs.princeton.edu/~appel/modern/ml/)
  by Andrew W. Appel.

### Grades
  - 40%: Team Programming Project
  - 20%: Midterm Exam
  - 20%: Final Exam (cumulative)
  - 20%: Three individual homework assignments

### TENTATIVE Syllabus (Subject to change!)

| Date      | Session | Lecture | Due |
| ----------- | ----------- |  ----------- |  ----------- |
| Wed Jan 23  | 1  | [Intro](./lectures/intro.pdf) | |
| Mon Jan 28  | 2  | [Language Translators](./lectures/translators.pdf)  | |
| Wed Jan 30  | 3  | [Basic Elements of PL](./lectures/languages.pdf) | |
|    |   | [Some Outstanding Projects](./lectures/projects.pdf) | |
| Mon Feb 4   | 4  | [Programming in OCaml](./lectures/ocaml.pdf) | |
| Wed Feb 6   | 5  | " | |
| Mon Feb 11  | 6  | "| |
| Wed Feb 13  | 7  | " | [Proposal](./assignments/proposal.html) |
| Mon Feb 18  | 8  | [Scanning](./lectures/scanner.pdf) | |
| Wed Feb 20  | 9  | " | [HW1](./assignments/hw1.html) |
| Mon Feb 25  | 10 | [Parsing I](./lectures/syntax.pdf) | |
| Wed Feb 27  | 11 | [Parsing II](./lectures/syntax2.pdf) | |
| Mon Mar 4   | 12 | Parsing III | |
| Wed Mar 6   | 13 | Types and Static Semantics | [LRM](./assignments/lrm.html) |
| Mon Mar 11  | 14 | " | HW2 |
| **Wed Mar 13**  |    | **Midterm Exam** | |
| **Mar 18 - 22** |    | **Spring Break** | |
| Mon Mar 25  | 15 | The MicroC Compiler | |
| Wed Mar 27  | 16 | " | |
| Mon Apr 1   | 17 | Runtime Environment | Hello World |
| Wed Apr 3   | 18 | " | |
| Mon Apr 8   | 19 | " | |
| Wed Apr 10  | 20 | Code Generation | |
| Mon Apr 15  | 21 | " | |
| Wed Apr 17  | 22 | Compiler Optimization | |
| Mon Apr 22  | 23 | " | HW3 |
| Wed Apr 24  | 24 | The Lambda Calculus | |
| Mon Apr 29  | 25 | " | |
| Wed May 1   | 26 | Review for Final  | |
| **Mon May 6**   |    | **Final Exam**  | |
| **Wed May 15**  |    | **Project Presentation**  | Project Reports |

### Sample Proposals
- [GRAIL: A Graph-Construction Language](http://www.cs.columbia.edu/~sedwards/classes/2017/4115-spring/proposals/GRAIL.pdf)
- [FRY - A Flat File Data Processing Language](http://www.cs.columbia.edu/~sedwards/classes/2014/w4115-fall/proposals/FRY.pdf)
- [Fly Language](http://www.cs.columbia.edu/~sedwards/classes/2016/4115-spring/proposals/Fly.pdf)
- [SetC: A Concise Set Language](http://www.cs.columbia.edu/~sedwards/classes/2017/4115-spring/proposals/SetC.pdf)
- [Coral Programming Language Proposal](http://www.cs.columbia.edu/~sedwards/classes/2018/4115-fall/proposals/Coral.pdf)
