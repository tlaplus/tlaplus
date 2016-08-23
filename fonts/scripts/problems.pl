#!/usr/bin/perl -w

# $Id$

# possible problems finder
# (c)2004,2005 Stepan Roh (PUBLIC DOMAIN)
# usage: ./problems.pl [-l <0|1|2|3>] sfd_files+

# detected problems (higher levels contain lower levels):
#   level 0:
#     monospaced font (with Mono in name) without indication in Panose (and vice-versa)
#     glyphs in monospaced face with different width
#     not normalized file (looks for WinInfo, DisplaySize, HStem, VStem, Ref, KernsSLIF, different position than encoding,
#       unordered glyphs or H or M flag)
#     glyphs without width or with negative width
#     duplicate glyphs
#     combining marks with non-zero width in non-monospaced fonts
#     missing point numbers in splines
#   level 1 (default):
#     colorized glyphs with content
#   level 2:
#     different set of mapped content glyphs (first SFD file specified on command line is taken as an etalon)
#   level 3:
#     ligature referencing colorized or missing glyphs
#     ligature in colorized glyph (due to bug in FF <20050502 it causes problems on Mac OS X)
#     ligature in empty glyph

sub process_sfd_file($$);

# glyph name => ( 'dec_enc' => dec_enc, 'hex_enc' => hex_enc )
%glyphs = ();
$glyphs_loaded = 0;
%problems_counter = ();

sub process_sfd_file($$) {
  local ($sfd_file, $max_level) = @_;
  
  sub problem($@) {
    my ($level, $problem, @args) = @_;
    
    if ($level <= $max_level) {
      print $sfd_file, ': [', $level, '] ', $problem, ': ', @args, "\n";
      $problems_counter{'['.$level.'] '.$problem}++;
    }
  }

  sub is_combining($) {
    my ($dec_enc) = @_;
    
    return (($dec_enc >= 0x0300) && ($dec_enc <= 0x036F))
        || (($dec_enc >= 0x1DC0) && ($dec_enc <= 0x1DFF))
        || (($dec_enc >= 0x20D0) && ($dec_enc <= 0x20FF))
        || (($dec_enc >= 0xFE20) && ($dec_enc <= 0xFE2F));
  }
  
  my $curchar = '';
  my $hex_enc = '';
  my $dec_enc = 0;
  my $colorized;
  my $flags;
  my ($fontname, $panose, $is_mono_name, $is_mono_panose) = ('', '', 0, 0);
  my $is_mono = 0;
  my $font_width = -1;
  my $curwidth = 0;
  my $has_ligature = 0;
  my $is_empty = 1;
  my %content_glyphs = ();
  my @ligature_refs = ();
  my %all_glyphs = ();
  my $prev_enc = -1;
  my $in_spline_set = 0;
  my $has_splines;
  my $has_refs;
  my %all_names = ();
  open (SFD, $sfd_file) || die "Unable to open $sfd_file : $!\n";
  while (<SFD>) {
    if (/^StartChar:\s*(\S+)\s*$/) {
      $curchar = $1;
      if (exists($all_names{$curchar})) {
	problem (0, 'duplicate glyph name', $1);
      }
      $all_names{$curchar} = 1;
      $hex_enc = '';
      $dec_enc = 0;
      $curwidth = -1;
      undef $colorized;
      undef $flags;
      $has_ligature = 0;
      @ligature_refs = ();
      $is_empty = 1;
      $in_spline_set = 0;
      $has_splines = 0;
      $has_refs = 0;
    } elsif (/^Colour:\s*(\S+)\s*/) {
      $colorized = $1;
    } elsif (/^Flags:\s*(\S+)\s*/) {
      $flags = $1;
      if ($flags =~ /([MH])/) {
        problem (0, 'not normalized: '.$1.' flag', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': flags=', $flags);
      }
    } elsif (/^Encoding:\s*(\d+)\s*((?:-|\d)+)\s*(\d+)\s*$/) {
      $dec_enc = $1;
      if ($2 > -1) {
        $hex_enc = sprintf ('%04x', $2);
      }
      if ($dec_enc != $3) {
        problem (0, 'not normalized: glyph position differs from encoding', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': position=', $3);
      }
      if ($dec_enc <= $prev_enc) {
        problem (0, 'not normalized: unordered glyphs', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': previous=', $prev_enc);
      }
      $prev_enc = $dec_enc;
    } elsif (/^Width:\s*(\S+)\s*/) {
      $curwidth = $1;
    } elsif (/^Ligature:\s*\S*\s*\S*\s*\S*\s*(.*?)\s*$/) {
      @ligature_refs = split(/\s+/, $1);
      $has_ligature = 1;
    } elsif (/^SplineSet\s*$/) {
      $is_empty = 0;
      $in_spline_set = 1;
      problem (0, 'mixed content', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : '')) if ($has_refs);
      $has_splines = 1;
    } elsif (/^EndSplineSet\s*$/) {
      $in_spline_set = 0;
    } elsif ($in_spline_set && !/.+,.+,.+$/) {
      problem (0, 'point numbers missing', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
    } elsif (/^Ref:/) {
      $is_empty = 0;
      problem (0, 'not normalized: old-style "Ref"', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
    } elsif (/^Refer:\s*\d+\s*\d+\s*\S\s*(-?\d+(?:\.\d*)?(?:e-?\d+)?)\s*(-?\d+(?:\.\d*)?(?:e-?\d+)?)\s*(-?\d+(?:\.\d*)?(?:e-?\d+)?)\s*(-?\d+(?:\.\d*)?(?:e-?\d+)?)\s*-?\d+(?:\.\d*)?(?:e-?\d+)?\s*-?\d+(?:\.\d*)?(?:e-?\d+)?\s*(\d+)/) {
      $is_empty = 0;
      if (($5 & 0x2) != 0x2) {
        problem (0, 'reference is not rounded to grid', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ' flags=', $5);
      }
      if (!(($1 == 1) && ($2 == 0) && ($3 == 0) && ($4 == 1))) {
        problem (0, 'transformed reference', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
      }
      problem (0, 'mixed content', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : '')) if ($has_splines);
      $has_refs = 1;
    } elsif (/^DisplaySize:/) {
      problem (0, 'not normalized: DisplaySize');
    } elsif (/^WinInfo:/) {
      problem (0, 'not normalized: WinInfo');
    } elsif (/^HStem:/) {
      problem (0, 'not normalized: HStem');
    } elsif (/^VStem:/) {
      problem (0, 'not normalized: VStem');
    } elsif (/^KernsSLIF:/) {
      problem (0, 'not normalized: KernsSLIF');
    } elsif (/^EndChar\s*$/) {
      if (!defined $colorized && !$is_empty) {
        $content_glyphs{$curchar}{'dec_enc'} = $dec_enc;
        $content_glyphs{$curchar}{'hex_enc'} = $hex_enc;
        @{$content_glyphs{$curchar}{'ligature'}} = @ligature_refs;
        # only mapped glyphs
        if ($hex_enc) {
          if ($glyphs_loaded) {
            if (!exists $glyphs{$curchar}) {
              problem (2, 'etalon-free glyph', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
            }
          } else {
            $glyphs{$curchar}{'dec_enc'} = $dec_enc;
            $glyphs{$curchar}{'hex_enc'} = $hex_enc;
          }
        }
      }
      if (defined $colorized && !$is_empty) {
        problem (1, 'colorized content', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : '') , ': color=', $colorized);
      }
      if (defined $colorized && defined $flags && ($flags =~ /W/)) {
        problem (1, 'colorized content', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : '') , ': color=', $colorized, ', flags=', $flags);
      }
      if (!$is_mono && defined $colorized && ($curwidth != 2048) && ($curwidth != 0)) {
        problem (1, 'colorized content', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : '') , ': color=', $colorized, ', width=', $curwidth);
      }
      if ($curwidth == -1) {
        problem (0, 'glyph w/o width', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
      } elsif ($curwidth < 0) {
        problem (0, 'negative width', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': width=', $curwidth);
      } elsif ($is_mono && defined $flags && ($flags =~ /W/)) {
        if ($font_width == -1) {
          $font_width = $curwidth;
        } elsif ($curwidth != $font_width) {
          problem (0, 'incorrect width', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': font width=', $font_width, ', glyph width=', $curwidth);
        }
      } elsif (!$is_mono && is_combining($dec_enc) && ($curwidth != 0) && !$is_empty) {
        problem (0, 'combining mark with non-zero width', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': width=', $curwidth);
      }
      if (defined $colorized && $has_ligature) {
        problem (3, 'colorized ligature', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': color=', $colorized);
      }
      if ($is_empty && $has_ligature) {
        problem (3, 'empty ligature', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
      }
      if (exists $all_glyphs{$dec_enc}) {
        problem (0, 'duplicate', $curchar, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
      }
      $all_glyphs{$dec_enc} = 1;
    } elsif (/^FontName:\s*(.*?)\s*$/) {
      $fontname = $1;
      $is_mono_name = ($fontname =~ /mono/i);
      $is_mono = 1 if ($is_mono_name);
    } elsif (/^Panose:\s*(.*?)\s*$/) {
      $panose = $1;
      $is_mono_panose = ((split(/\s+/, $panose))[3] == 9);
      $is_mono = 1 if ($is_mono_panose);
    }
  }
  close (SFD);
  if ($is_mono_name != $is_mono_panose) {
    problem (0, 'mixed monospace', 'font name=', $fontname, ', panose=', $panose);
  }
  foreach $glyph (sort { $content_glyphs{$a}{'dec_enc'} <=> $content_glyphs{$b}{'dec_enc'} } keys %content_glyphs) {
    my $dec_enc = $content_glyphs{$glyph}{'dec_enc'};
    my $hex_enc = $content_glyphs{$glyph}{'hex_enc'};
    foreach $liga (@{$content_glyphs{$glyph}{'ligature'}}) {
      if (!exists ($content_glyphs{$liga})) {
        problem (3, 'ligature references colorized or missing glyph', $glyph, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''), ': ligature ref=', $liga);
      }
    }
  }
  if ($glyphs_loaded) {
    foreach $glyph (sort { $glyphs{$a}{'dec_enc'} <=> $glyphs{$b}{'dec_enc'} } keys %glyphs) {
      my $dec_enc = $glyphs{$glyph}{'dec_enc'};
      my $hex_enc = $glyphs{$glyph}{'hex_enc'};
      if (!exists $content_glyphs{$glyph}) {
        problem (2, 'missing glyph', $glyph, ' ', $dec_enc, ($hex_enc ? ' U+'.$hex_enc : ''));
      }
    }
  }
  $glyphs_loaded = 1;
}

if (!@ARGV) {
  print STDERR "usage: [-l <0|1|2|3>] sfd_files+\n";
  exit 1;
}

$max_level = 1;
if ($ARGV[0] eq '-l') {
  shift @ARGV;
  $max_level = shift @ARGV;
}
@sfd_files = @ARGV;

foreach $sfd_file (@sfd_files) {
  process_sfd_file ($sfd_file, $max_level);
}

foreach $problem (sort keys %problems_counter) {
  print $problems_counter{$problem}, ' problems of type "', $problem, '"', "\n";
}

1;
