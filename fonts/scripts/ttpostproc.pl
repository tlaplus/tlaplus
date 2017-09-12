#!/usr/bin/perl -w
# $Id$

# TTF postprocessing
# usage:
#   chmod +x ttpostproc.pl
#   ./ttpostproc.pl generated/*.ttf

use Font::TTF::Font;

sub postproc($) {
  my ($file) = @_;
  my $backup = $file.'~';

  rename($file, $backup) || die "Unable to rename $f as $backup : $!\n";

  $font = Font::TTF::Font->open($backup) || die "Unable to open font $backup : $!\n";

  # head.flags:
  #      1 => baseline for font at y=0
  #      2 => left sidebearing point at x=0
  #      4 => instructions may depend on point size
  #      8 => force ppem to integer values for all internal scaler math
  #   0x10 => instructions may alter advance width
  $font->{'head'}->{'flags'} = 1 + 2 + 4 + 8 + 0x10;
  
  # gasp table
  #   version = 0
  #   numRanges = 2
  #   range[0].rangeMaxPPEM = 8
  #   range[0].rangeGaspBehavior = 2 (GASP_DOGRAY)
  #   range[1].rangeMaxPPEM = 65535 (max.)
  #   range[1].rangeGaspBehavior = 3 (GASP_DOGRAY|GASP_GRIDFIT)
  $gasp_data = pack('nnnnnn', 0, 2, 8, 2, 0xffff, 3);
  $font->{'gasp'} = Font::TTF::Table->new(( 'dat' => $gasp_data ));
  
  $font->out($file) || die "Unable to write to $file : $!\n";
  $font->release();
}

@files = @ARGV;
foreach $f (@files) {
  postproc($f);
}

1;
