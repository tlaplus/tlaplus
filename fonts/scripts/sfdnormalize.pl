#!/usr/bin/perl -w

# $Id$

# SFD normalizer (discards GUI information from SFD files)
# (c)2004,2005 Stepan Roh (PUBLIC DOMAIN)
# usage: ./sfdnormalize.pl sfd_file(s)
#  will create files with suffix .norm

# changes done:
#   WinInfo - discarded
#   DisplaySize
#           - discarded
#   Flags   - discarded O (open), H (changed since last hinting - useless for TTF), M (manual hinting - useless for TTF)
#   Refer   - changed S (selected) to N (not selected)
#   Fore, Back, SplineSet, Grid
#           - all points have 4 masked out from flags (selected)
#             and 256 (do not interpolate)
#   HStem, VStem
#           - discarded (those are Type1 stems = PS hints)
#   recalculate number of characters and positional encoding
#   NameList
#           - discarded (temporary)
#   ModificationTime - discarded
#   CreationTime - discarded
#   VWidth - discarded (for now)
#   TeXData - discarded
#   TeX - discarded
#   Validated - discarded
#   UndoRedoHistory - discarded
# changes making it incompatible with FF older than (approx.) 20050728:
#   Ref     - renamed to Refer
#   KernsSLIF
#           - renamed to KernsSLIFO

# !!! Always review changes done by this utility !!!

sub process_sfd_file($);

sub process_sfd_file($) {
  my ($sfd_file) = @_;

  my $out = $sfd_file . '.norm';
  
  open (SFD, $sfd_file) || die "Unable to open $sfd_file : $!\n";
  open (OUT, '>'.$out) || die "Unable to open $out : $!\n";

  my $curchar = '';
  my %glyphs = ();
  my $in_spline_set = 0;
  my $max_dec_enc = 0;
  my %pos_glyphs_map = ();
  my $in_undo_redo = 0;

  while (<SFD>) {
    next if (/^(WinInfo|DisplaySize|HStem|VStem|ModificationTime|CreationTime|VWidth|TeX|TeXData|Validated|AltUni2):/);
    next if (/^$/);
    s,^(NameList:).*$,$1 AGL without afii,;
    s,^Ref:,Refer:,;
    s,^KernsSLIF:,KernsSLIFO:,;
    s,^(Flags:.*?)O(.*)$,$1$2,;
    s,^(Flags:.*?)H(.*)$,$1$2,;
    s,^(Flags:.*?)M(.*)$,$1$2,;
    # remove empty Flags line
    next if (/^Flags:\s*$/);
    s,^(Refer:.*?)S(.*)$,$1N$2,;
    if (/^(Fore|Back|SplineSet|Grid)\s*$/) {
      $in_spline_set = 1;
    } elsif (/^EndSplineSet\s*$/) {
      $in_spline_set = 0;
    } elsif ($in_spline_set) {
      s/(\s+)(\S+?)(,\S+\s*)$/$1.($2 & ~4 & ~256).$3/e;
      s/([\s^])-0(\s)/$1."0".$2/eg
    }
    #remove UndoRedoHistory block
    if (/^UndoRedoHistory/) {
      $in_undo_redo = 1; next
    } elsif (/^EndUndoRedoHistory/) {
      $in_undo_redo = 0; next
    }
    next if ($in_undo_redo);
    if (/^BeginChars:/) {
      $in_chars = 1;
    } elsif (/^EndChars\s*$/) {
      $in_chars = 0;
      # adding of 1 to max_dec_enc is strange, but works
      # second parameter is set to 0 to avoid merging conflicts (fontforge ignores anyway)
      print OUT "BeginChars: ", $max_dec_enc + 1, " 0\n";
      foreach $glyph (sort { $glyphs{$a}{'dec_enc'} <=> $glyphs{$b}{'dec_enc'} } keys %glyphs) {
        print OUT "StartChar: ", $glyphs{$glyph}{'name'}, "\n";
        my $dec_enc = $glyphs{$glyph}{'dec_enc'};
        my $mapped_enc = $glyphs{$glyph}{'mapped_enc'};
        print OUT "Encoding: ", $dec_enc, " ", $mapped_enc, " ", $dec_enc, "\n";
        # recalculate references and kerning pairs
        foreach $l (@{$glyphs{$glyph}{'lines'}}) {
          $l =~ s/^(Refer:\s*)(\S+)/$1.(exists $pos_glyphs_map{$2} ? $pos_glyphs_map{$2} : (warn "Glyph $glyph ($dec_enc) has reference to unknown glyph position $2\n", $2))/e;
          if ($l =~ /^KernsSLIFO:\s*(.*)$/) {
            my @nums = split(/\s+/, $1);
            if ((scalar (@nums) % 4) != 0) {
              warn "Kerning definition in glyph $curchar ($dec_enc) is malformed and won't be remapped\n";
            } else {
              for (my $i = 0; $i < scalar (@nums); $i += 4) {
                my $pos = $nums[$i];
                if (exists $pos_glyphs_map{$pos}) {
                  $nums[$i] = $pos_glyphs_map{$pos};
                } else {
                  warn "Glyph $glyph ($dec_enc) has kerning reference to unknown glyph position $pos\n";
                }
              }
            }
            $l = "KernsSLIFO: " . join(' ', @nums) . "\n";
          }
          print OUT $l;
        }
        print OUT "EndChar\n";
        $pos++;
      }
      print OUT "EndChars\n";
    } elsif (/^StartChar:\s*(\S+)\s*$/) {
      my $name = $1;
      $curchar = $name;
      while (exists $glyphs{$curchar}) {
        $curchar .= '#';
      }
      $glyphs{$curchar}{'name'} = $name;
    } elsif (/^Encoding:\s*(\d+)\s*((?:-|\d)+)\s*(\d+)\s*$/) {
      $dec_enc = $1;
      $max_dec_enc = $dec_enc if ($dec_enc > $max_dec_enc);
      $mapped_enc = $2;
      $pos = $3;
      $glyphs{$curchar}{'dec_enc'} = $dec_enc;
      $glyphs{$curchar}{'mapped_enc'} = $mapped_enc;
      $glyphs{$curchar}{'pos'} = $pos;
      if (exists $pos_glyphs_map{$pos}) {
        warn "Glyph $curchar ($dec_enc) has duplicate glyph position $pos - won't be remapped - possible output corruption!\n";
      } else {
        $pos_glyphs_map{$pos} = $dec_enc;
      }
    } elsif (/^EndChar\s*$/) {
      $curchar = '';
    } else {
      if (!$in_chars) {
        print OUT;
      } elsif ($curchar eq '') {
        warn "Malformed input file $sfd_file?";
      } else {
        push (@{$glyphs{$curchar}{'lines'}}, $_);
      }
    }
  }

  close (SFD);
  close (OUT);
}

if (!@ARGV) {
  print STDERR "usage: sfd_files+\n";
  exit 1;
}

@sfd_files = @ARGV;

foreach $sfd_file (@sfd_files) {
  process_sfd_file ($sfd_file);
}

1;
