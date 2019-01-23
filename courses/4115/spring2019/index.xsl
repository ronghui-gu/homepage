<?xml version="1.0" encoding="ISO-8859-1"?>
<xsl:stylesheet
   version="1.0"
   xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:output method="html" version="1.0" encoding="iso-8859-1" indent="yes"/>

  <xsl:template match="/">

    <html>
      <head>
	<title>COMS W4115 Programming Languages and Translators</title>
	<meta http-equiv="Content-Type"
	      content="text/html; charset=ISO-8859-1"/>
	<link rel="stylesheet" href="class.css"/>  
      </head>

      <body>

	<table width="550" border="0" cellspacing="0" cellpadding="0"
	       class="title">
	  <tr>
	    <td colspan="2">
	      <a href="http://www.cs.columbia.edu/~sedwards/">
		<img src="../../../images/name.gif"
		     width="308" height="27" alt="Stephen A. Edwards"/>
	      </a>
	    </td>
	    <td align="right" rowspan="2">
	      <a href="http://www.cs.columbia.edu/">
		<img src="../../../images/crown.gif" width="85" height="75"
		     alt="Columbia University Crown"/></a>
	    </td>
	  </tr>
	  <tr>
	    <td></td>
	    <td>COMS W4115 <br/> Programming Languages and Translators <br/>
	      <xsl:value-of select="/class/@edition" />
	    </td>
	  </tr>
	</table>

	<h1>Lectures</h1>

	<p>
	  Class meets <xsl:value-of select="/class/classtime/@time"/>
	  <xsl:text> </xsl:text>
	  <xsl:value-of select="/class/classtime/@location"/>.
	</p>

	<h1>Staff</h1>

	<xsl:apply-templates select="/class/staff"/>

	<h1>Overview</h1>

	<p>The goal of PLT is to teach you both about the structure of
	  computer programming languages and the basics of implementing
	  compilers for such languages.</p>

	<p>The course will focus mostly on traditional imperative and
	  object-oriented languages, but will also cover functional and logic
	  programming, concurrency issues, and some aspects of scripting
	  languages.  Homework and tests will cover language issues.  You will
	  design and implement a language of your own design in a semester-long
	  team project.</p>

	<p>While few of you will ever implement a full commercial compiler
	  professionally, the concepts, techniques, and tools you will learn
	  have broad application.</p>

	<h1>Prerequisites</h1>

	<p>COMS W3157 Advanced Programming: You will
	  be dividing into teams to build a compiler, so you need to have some
	  idea how to keep this under control.  Quick test: you need to know
	  about Makefiles and source code control systems.</p>

	<p>COMS W3261 Computability and Models of Computation: You will
	  need an understanding of formal languages and grammar to build the
	  parser and lexical analyzer.  Quick test: you must know about regular
	  expressions, context-free grammars, and NFAs.</p>

	<h1>Schedule</h1>

	<xsl:apply-templates select="/class/schedule"/>

<iframe src="https://calendar.google.com/calendar/embed?src=882f8fqcbhujrl3fcvpscdmqns%40group.calendar.google.com&amp;ctz=America/New_York" style="border: 0" width="800" height="600" frameborder="0" scrolling="no"></iframe>

	<h1>Suggested Text</h1>

	<table>
	  <tr>
	    <td>
	      <p>
		Alfred V. Aho, Monica Lam, Ravi Sethi, and Jeffrey D. Ullman. <br/>
		<i>Compilers: Principles, Techniques, and Tools</i>. <br/>
		Addison-Wesley, 2006. Second Edition. <br/>
		<br/>
		The first edition was long the standard text on
		compilers; the second edition of the "dragon
		book" has now been updated and continues to be
		one of the more readable books on the topic.
		Columbia's own Prof. Al Aho is one of the authors.
	      </p>
	    </td>
	    <td>
	      <img src="/~sedwards/images/dragonbook2e.jpg" alt="Cover of the Dragon Book 2nd edition"
		   width="95" height="144"/>
	    </td>
	  </tr>
	</table>

	<h1>Related Texts</h1>

	<table><tr><td>
	      <p>
		Michael L. Scott. <br/>
		<a href="http://www.cs.rochester.edu/~scott/pragmatics/"><i>Programming Language Pragmatics</i></a> <br/>
		Morgan Kaufmann, 2006.  Second Edition. <br/>
		<br/>
		A broad-minded book about languages in general, but has less on
		practical details of compiler construction.
	      </p>
	    </td>
	    <td>
	      <a href="http://www.cs.rochester.edu/~scott/pragmatics/">
		<img src="/~sedwards/images/scott2e.jpg"
		     alt="Cover of Programming Language Pragmatics 2nd edition"
		     width="95" height="126"/></a>
	    </td>
	  </tr>

	  <tr>
	    <td>
	      <p>
		Andrew W. Appel. <br/>
		<a href="http://www.cs.princeton.edu/~appel/modern/ml/">
		  <i>Modern Compiler Implementation in ML</i></a>. <br/>
		Cambridge University Press, 1998. <br/>
		<br/>
		The opposite of Scott: focuses on compiler construction, not language
		design issues.<br/>
		It uses the functional language ML, which is closely related to O'Caml,
		but just different enough to be annoying.
	      </p>
	    </td>
	    <td>
	      <img src="/~sedwards/images/appel-ml.jpg" alt="Cover of Appel"
		   width="94" height="125"/>
	    </td>
	  </tr>

	  <tr>
	    <td>
	      <p>
		Lawrence C. Paulson<br/>
		<a href="http://www.cl.cam.ac.uk/~lp15/MLbook/">
		  <i>ML for the Working Programmer</i></a>. <br/>
		Cambridge University Press, 1996.  Second edition.<br/>
		<br/>
		A book about functional programming.  It's written for the ML
		language, not O'Caml, but the two are closely related.
	      </p>
	    </td>
	    <td>
	      <img src="/~sedwards/images/ml-working-programmer.jpg" alt="Cover of Paulson"
		   width="99" height="125"/>
	    </td>
	  </tr>

	  <tr>
	    <td>
	      <p>
		Steven S. Muchnick <br/>
		<i>Advanced Compiler Design and Implementation</i>. <br/>
		Morgan Kaufmann, 1997. <br/>
		<br/>
		A very extensive book on many aspects of compiler design.  Starts
		about halfway through Appel and goes much farther.  Recommended for
		serious compiler hackers only.
	      </p>
	    </td>
	    <td>
	      <img src="/~sedwards/images/muchnick.jpg" alt="Cover of Muchnick"
		   width="107" height="140"/>
	    </td>
	  </tr>

	</table>

	<h1>Objective Caml Resources</h1>

	<table>
	  <tr>
	    <td valign="top">
	      <a href="http://caml.inria.fr/">
		<img src="homeicon.gif" alt="webpage"/></a>
	    </td>
	    <td>
	      The Caml Language Homepage.  Compiler downloads and
	      documentation.  Start here.
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="http://caml.inria.fr/pub/docs/manual-ocaml/index.html">
		<img src="homeicon.gif" alt="webpage"/></a>
	    </td>
	    <td>
	      The Objective Caml System.  Documentation and User's Manual for
	      the whole system, including documentation for ocamllex,
	      ocamlyacc, ocamldep, ocamldebug, and all the standard
	      libraries.
	    </td>
	  </tr>

<!--
	  <tr>
	    <td valign="top">
	      <a href="http://www.cs.caltech.edu/courses/cs134/cs134b/book.pdf">
		<img src="pdfsmall.gif" alt="PDF file"/></a>
	    </td>
	    <td>
	      Jason Hickey, <i>Introduction to Objective Caml</i>.  One of my
	      favorite books on O'Caml.
	    </td>
	  </tr>
-->

	  <tr>
	    <td valign="top">
	      <a href="http://caml.inria.fr/pub/docs/oreilly-book/">
		<img src="homeicon.gif" alt="webpage"/></a>
	    </td>
	    <td>
	      Emmanuel Chailloux, Pascal Manoury, and Bruno
	      Pagano, <i>Developing Applications with Objective Caml</i>.  An
	      online book translated from the French (O'Reilly).
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="http://mirror.ocamlcore.org/ocaml-tutorial.org/">
		<img src="homeicon.gif" alt="webpage"/></a>
	    </td>
	    <td>
	      Objective CAML Tutorial
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="calculator.tar.gz">
		<img src="downicon.gif" alt=".tar.gz file"/></a>
	    </td>
	    <td>
	      OCaml source for the four-function calculator.
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="microc.tar.gz">
		<img src="downicon.gif" alt=".tar.gz file"/></a>
	    </td>
	    <td>
	      OCaml source and test cases for the MicroC language, which
	      generates LLVM IR.
	    </td>
	  </tr>
	  
	</table>

	<h1>The Project</h1>

	<p>The focus of 4115 is the design and implementation of a little
	  language.  You will divide into teams and design the goals, syntax,
	  and semantics of your language, and implement a compiler for your
	  language.</p>

	<p>
	  Exception: CVN students will do the project individually.
	</p>

	<h1>Final Report Outline</h1>

	<p>
	  This is a critical part of the project and will be a
	  substantial fraction of the grade.
	</p>

	<p>
	  Include the following sections:
	</p>

	<ol>
	  <li>Introduction
	    <ul><li>Include your language white paper.</li></ul>
	  </li>

	  <li>Language Tutorial
	    <ul>
	      <li>A short explanation telling a novice how to use your
		language.</li>
	    </ul>
	  </li>

	  <li>Language Manual
	    <ul>
	      <li>Include your language reference manual.</li>
	    </ul>
	  </li>

	  <li>Project Plan

	    <ul>
	      <li>Identify process used for planning, specification, development
		and testing</li>
	      <li>Include a one-page programming style guide used by the team</li>
	      <li>Show your project timeline</li>
	      <li>Identify roles and responsibilities of each team member</li>
	      <li>Describe the software development environment used (tools and
		languages)</li>
	      <li>Include your project log</li>
	    </ul>

	  </li>

	  <li>Architectural Design

	    <ul>
	      <li>Give block diagram showing the major components of your translator</li>
	      <li>Describe the interfaces between the components</li>
	      <li>State who implemented each component</li>
	    </ul>

	  </li>

	  <li>Test Plan

	    <ul>
	      <li>Show two or three representative source language programs along
		with the target language program generated for each</li>
	      <li>Show the test suites used to test your translator</li>
	      <li>Explain why and how these test cases were chosen</li>
	      <li>What kind of automation was used in testing</li>
	      <li>State who did what</li>
	    </ul>
	  </li>

	  <li>Lessons Learned

	    <ul>
	      <li>Each team member should explain his or her most important
		learning</li>
	      <li>Include any advice the team has for future teams</li>
	    </ul>

	  </li>

	  <li>Appendix
	    <ul>
	      <li>Attach a complete code listing of your
		translator with each module signed by its author</li>
	      <li> Do <em>not</em> include any automatially generated files, only the
		sources.</li>
	    </ul>
	  </li>

	</ol>

	<h1>Project Resources</h1>

	<table>

	  <tr>
	    <td valign="top">
	      <a href="../../2003/w4115/cvs.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      A two-page introduction to the CVS version control system.
	      <em>I strongly suggest you keep your project under some version
		control system.</em>
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="../../2012/w4115-fall/reports/Funk.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      An excellent final report: the Funk language by 4115 students
	      Naser AlDuaij, Senyao Du, Noura Farra, Yuan Kang, and
	      Andrea Lottarini.
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="../../2014/w4115-fall/reports/Sheets.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      An excellent final report: the Sheets language by 4115 students
	      Benjamin Barg, Gabriel Blanco, Amelia Brunner, and Ruchir Khaitan.
	    </td>
	  </tr>


	</table>

	<h1>Language Reference Manuals</h1>

	<table>

	  <tr>
	    <td valign="top">
	      <a href="/~sedwards/papers/cman.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      Dennis M. Ritchie,
	      <a href="https://www.bell-labs.com/usr/dmr/www/cman.pdf">C Reference Manual</a>
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="http://s3-us-west-2.amazonaws.com/belllabs-microsite-dritchie/cbook/index.html">
		<img src="homeicon.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      Kernighan &amp; Ritchie, <a href="http://s3-us-west-2.amazonaws.com/belllabs-microsite-dritchie/cbook/index.html">The C Programming Language</a>
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="/~sedwards/papers/sgi1999c.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>The C Language Reference Manual (SGI)
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="http://www.stroustrup.com/C++.html">
		<img src="homeicon.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      Stroustrup, <a href="http://www.stroustrup.com/C++.html">The C++ Programming Language</a>
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="/~sedwards/papers/gosling2000java.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      <a href="http://docs.oracle.com/javase/specs/">The Java Language Specification</a>
	    </td>
	  </tr>

	  <tr>
	    <td valign="top">
	      <a href="/~sedwards/papers/microsoft2001csharp.pdf">
		<img src="pdfsmall.gif" alt="pdf"/></a>
	    </td>
	    <td>
	      The C# Language Specification
	    </td>
	  </tr>

<!--
	  <tr>
	    <td valign="top">
	      <a href="http://cm.bell-labs.com/cm/cs/awkbook/index.html">
		<img src="homeicon.gif" alt="home"/></a>
	    </td>
	    <td>
	      Aho, Kernighan, and Weinberger,
	      <a href="http://cm.bell-labs.com/cm/cs/awkbook/index.html">
		The AWK Programming Language</a>
	    </td>
	  </tr>
-->

	</table>

	<h1>Projects</h1>


	<xsl:apply-templates select="/class/teams"/>

    <p>
      <img src="../../../icons/staricon.png" width="16" height="16" alt="star"/>
      My favorites
    </p>


	<h1>Grading</h1>

	<table>
	  <tr><td>40 % Project</td></tr>
	  <tr><td>20 % Midterm</td></tr>
	  <tr><td>30 % Final</td></tr>
	  <tr><td>10 % Homework</td></tr>
	</table>

	<h1>Collaboration</h1>

	<p>
	  You will collaborate with your own small team
	  on the programming project, but you may not collaborate with others on
	  homeworks.  Teams may share ideas about the programming assignments,
	  but not code.  Any two teams found submitting similar code will
	  receive zero credit for the whole assignment, and repeat offenses will
	  be referred to the dean.  See
	  <a href="http://www.cs.columbia.edu/education/honesty/">the 
	    Columbia CS department academic policies</a> for more details.
	</p>


	<h1>Other</h1>

	<p>
	  <a href="http://validator.w3.org/check?uri=referer">
	    <img src="http://www.w3.org/Icons/valid-html401"
		 alt="Valid HTML 4.01" height="31" width="88"/></a>
	  <a href="http://jigsaw.w3.org/css-validator/">
	    <img style="border:0;width:88px;height:31px"
		 src="http://jigsaw.w3.org/css-validator/images/vcss" 
		 alt="Valid CSS"/>
	  </a>
	</p>

      </body>
    </html>
  </xsl:template>

  <xsl:template match="staff">
    <table class="staff">
      <tr>
	<th>Name</th>
	<th>Email</th>
	<th>Office hours</th>
	<th>Location</th>
      </tr>

      <xsl:for-each select="member">
	<tr>
	  <td><xsl:value-of select="@name" /></td>
	  <td><a>
	      <xsl:attribute name="href">mailto:<xsl:value-of select="@email" />?subject=[CSEE%25203827]</xsl:attribute>
	      <xsl:value-of select="@email" />
	    </a>
	  </td>
	  <td><xsl:value-of select="@hours" /></td>
	  <td><xsl:value-of select="@location" /></td>
	</tr>
      </xsl:for-each>

    </table>
  </xsl:template>

  <xsl:template match="schedule">
    <table class="schedule" border="0" cellspacing="0" cellpadding="4">
      <tr>
	<th>Date</th>
	<th>Session</th>
	<th>Lecture</th>
	<th>Notes</th>
	<th>Reading</th>
	<th>Due</th>
      </tr>

      <xsl:for-each select="day">
	<xsl:variable name="num" select="@num" />
	<tr>
	  <xsl:choose>

	    <xsl:when test="@event">
	      <xsl:attribute name="class">holiday</xsl:attribute>
	      <td><xsl:value-of select="@date" /></td>
	      <td/>
	      <td><xsl:value-of select="@event" /></td>
	      <td/>
	      <td/>
	      <td/>
	    </xsl:when>

	    <xsl:otherwise>
	      <xsl:attribute name="class">
		<xsl:choose>
		  <xsl:when test="@num mod 2">even</xsl:when>
		  <xsl:otherwise>odd</xsl:otherwise>
		</xsl:choose>
	      </xsl:attribute>
	      <td><xsl:value-of select="@date" /></td>
	      <td>
		<xsl:for-each select="../lecture[@day=$num]">
		  <xsl:value-of select="@session" />
		  <br/>
		</xsl:for-each>
	      </td>
	      <td>
		<xsl:for-each select="../lecture[@day=$num]">
		  <xsl:value-of select="text()" />
		  <br/>
		</xsl:for-each>
	      </td>
	      <td>
		<xsl:for-each select="../lecture[@day=$num]">
		  <xsl:if test="@pdf">
		    <a>
		      <xsl:attribute name="href">
			<xsl:value-of select="@pdf"/>.pdf</xsl:attribute>
		      <img src="pdfsmall.gif" alt="pdf"/>
		    </a>
		    <br/>
		  </xsl:if>
		</xsl:for-each>
	      </td>
	      <td>
		<xsl:for-each select="../lecture[@day=$num]">
		  <xsl:value-of select="@reading" /><br/>
		</xsl:for-each>
	      </td>
	      <td>
		<xsl:for-each select="../assignment[@due=$num]">
		  <xsl:if test="@pdf">
		    <a>		    
		      <xsl:attribute name="href">
			<xsl:value-of select="@pdf"/>.pdf</xsl:attribute>
		      <img src="pdfsmall.gif" alt="pdf"/>
		    </a>
		    <xsl:text> </xsl:text>
		  </xsl:if>
		  <xsl:copy-of select="*|text()"/>
		</xsl:for-each>
	      </td>
	    </xsl:otherwise>

	  </xsl:choose>
	</tr>
      </xsl:for-each>
      
    </table>
  </xsl:template>

  <xsl:template match="teams">
    <table class="schedule" cellspacing="0" cellpadding="4">
      <xsl:for-each select="team">
	<xsl:sort select="@name" />
	<tr>
	  <xsl:attribute name="class">
	    <xsl:choose>
	      <xsl:when test="position() mod 2">even</xsl:when>
	      <xsl:otherwise>odd</xsl:otherwise>
	    </xsl:choose>
	  </xsl:attribute>

	  <td>
	    <b><xsl:value-of select="@name" /></b>:
	    <xsl:value-of select="@description" />
	    <xsl:if test="@ta != ''">
	      (<i><xsl:value-of select="@ta" /></i>)	      
	    </xsl:if>
	    <xsl:if test="@star != ''">
	      <img src="../../../icons/staricon.png"
		   width="16" height="16" alt="star"/>
	    </xsl:if>
	    <br />

	    <xsl:call-template name="document-link">
	      <xsl:with-param name="type" select="@proposal" />
	      <xsl:with-param name="team" select="@name" />
	      <xsl:with-param name="file"
			      select="concat('proposals/',@name)" />
	      <xsl:with-param name="title" select="'Proposal'" />
	    </xsl:call-template>

	    <xsl:call-template name="document-link">
	      <xsl:with-param name="type" select="@lrm" />
	      <xsl:with-param name="team" select="@name" />
	      <xsl:with-param name="file"
			      select="concat('lrms/',@name)" />
	      <xsl:with-param name="title" select="'LRM'" />
	    </xsl:call-template>

	    <xsl:call-template name="document-link">
	      <xsl:with-param name="type" select="@report" />
	      <xsl:with-param name="team" select="@name" />
	      <xsl:with-param name="file"
			      select="concat('reports/',@name)" />
	      <xsl:with-param name="title" select="'Final Report'" />
	    </xsl:call-template>

	    <xsl:call-template name="document-link">
	      <xsl:with-param name="type" select="@slides" />
	      <xsl:with-param name="team" select="@name" />
	      <xsl:with-param name="file"
			      select="concat('reports/',@name,'-presentation')" />
	      <xsl:with-param name="title" select="'Slides'" />
	    </xsl:call-template>

	    <xsl:call-template name="document-link">
	      <xsl:with-param name="type" select="@files" />
	      <xsl:with-param name="team" select="@name" />
	      <xsl:with-param name="file"
			      select="concat('reports/',@name)" />
	      <xsl:with-param name="title" select="'Project Files'" />
	    </xsl:call-template>

	    <br />

	    <xsl:for-each select="student">
	      <xsl:sort select="@lname" />
	      <xsl:if test="position() != 1">, 
		<xsl:if test="position() = last()">and </xsl:if>
	      </xsl:if>
	      <xsl:value-of select="@fname" />
	      <xsl:value-of select="' '" />
	      <xsl:value-of select="@lname" />
	    </xsl:for-each>



	  </td>
	</tr>
      </xsl:for-each>
    </table>

<!--
    <p>
      <img src="../../../icons/staricon.png" width="16" height="16" alt="star"/>
      My favorites
    </p>
-->

  </xsl:template>

  <xsl:template name="document-link">
    <xsl:param name="type" />
    <xsl:param name="team" />
    <xsl:param name="file" />
    <xsl:param name="title" />
    <xsl:if test="$type != ''">
      <a>
	<xsl:attribute name="href">
	  <xsl:value-of select="$file"/>.<xsl:value-of select="$type"/>
	</xsl:attribute>
	<xsl:choose>
	  <xsl:when test="$type='pdf'">	 
	    <img src="../../../icons/pdfsmall.gif" alt="pdf"
		 width="15" height="16" border="0"/>
	  </xsl:when>

	  <xsl:when test="$type='ppt' or $type='pptx'">	 
	    <img src="../../../icons/pptsmall.gif" alt="Powerpoint File"
		 width="15" height="16" border="0"/>
	  </xsl:when>

	  <xsl:when test="$type='tar.gz' or $type='zip' or $type='tar.bz2'">
	    <img src="../../../icons/downicon.gif"
		 width="16" height="22" border="0" alt="Archive"/>
	  </xsl:when>

	  <xsl:otherwise>UNRECOGNIZED FILETYPE</xsl:otherwise>

      </xsl:choose>

      <xsl:value-of select="$title" />
      </a>
      <xsl:text> </xsl:text>
    </xsl:if>
  </xsl:template>

</xsl:stylesheet>
