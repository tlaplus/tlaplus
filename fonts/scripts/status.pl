#!/usr/bin/perl -w

# $Id$

# status.txt file generator
# (c)2004 Stepan Roh (PUBLIC DOMAIN)
# usage: ./status.pl version_tag status_file sfd_files+
#   will print new status file on standard output

sub parse_status_file(\%$);
sub parse_sfd_file(\%$$);
sub print_status_file(\%);
sub parse_versions($);
sub format_versions(\%);
sub normalize_version($);
sub denormalize_version($);
sub detect_full_typefaces_support(@);

# internal parsed format:
# _ => ( header lines* )
# hexadecimal character encoding => ( 'name' => name, 'versions' => ( version => ( typefaces* ) ) )

$debug = 0;

$name_width = 20;

if ($debug) {
  use Data::Dumper;

  $Data::Dumper::Indent = 1;
  $Data::Dumper::Sortkeys = 1;
  $Data::Dumper::Purity = 1;
}

%parsed_typefaces = ();

sub normalize_version($) {
  my ($version) = @_;
  
  if ($version eq 'original') {
    $version = '0.0';
  }
  return join ('_', map { sprintf ("%02s", $_) } split (/\./, $version));
}

sub denormalize_version($) {
  my ($version) = @_;
  
  $version = join ('.', map { $_ + 0 } split (/_/, $version));
  if ($version eq '0.0') {
    $version = 'original';
  }
  return $version;
}

sub parse_versions($) {
  my ($versions) = @_;
  
  my %ret = ();
  while ($versions =~ s,^\s*(\S+)\s*(?:\((.*?)\)|),,) {
    my ($version, $typefaces) = ($1, $2);
    $version = normalize_version($version);
    if ($typefaces) {
      my @typefaces = split (/\s*,\s*/, $typefaces);
      $ret{$version} = \@typefaces;
    } else {
      $ret{$version} = [];
    }
  }
  return %ret;
}

sub parse_status_file(\%$) {
  my ($parsed_ref, $status_file) = @_;
  
  open (STATUS, $status_file) || die "Unable to open $status_file : $!\n";
  while (<STATUS>) {
    if (/^U+/) {
      my ($hex_enc, $name, $versions) = ($_ =~ /^U\+(\S+)\s+(\S+)\s+(.*?)\s*$/);
      my %versions = parse_versions ($versions);
      $$parsed_ref{$hex_enc}{'name'} = $name;
      $$parsed_ref{$hex_enc}{'versions'} = \%versions;
    } else {
      push (@{$$parsed_ref{'_'}}, $_);
    }
  }
  close (STATUS);
}

sub parse_sfd_file(\%$$) {
  my ($parsed_ref, $version_tag, $sfd_file) = @_;
  
  open (SFD, $sfd_file) || die "Unable to open $sfd_file : $!\n";
  my $typeface = '';
  my $curchar = '';
  my $hex_enc = '';
  my $empty = 0;
  $version_tag = normalize_version($version_tag);
  while (<SFD>) {
    if (/^FullName:\s+\S+\s+(.*?)\s*$/) {
      # DejaVu is not included in typeface
      $typeface = $1;
      $parsed_typefaces{$typeface} = 1;
    } elsif (/^StartChar:\s*(\S+)\s*$/) {
      $curchar = $1;
      $hex_enc = '';
      $empty = 0;
    } elsif (/^Colour:/) {
      # XXX this is quick'n'dirty hack to detect non-empty glyphs
      $empty = 1;
    } elsif (/^Encoding:\s*\d+\s*(\d+)\s*\d+\s*$/) {
      $hex_enc = sprintf ('%04x', $1);
    } elsif ($hex_enc && !$empty && /^EndChar\s*$/) {
      $$parsed_ref{$hex_enc}{'name'} = $curchar;
      push (@{$$parsed_ref{$hex_enc}{'versions'}{$version_tag}}, $typeface);
    }
  }
  close (SFD);
}

sub detect_full_typefaces_support(@) {
  my %typefaces = ();
  foreach $typeface (@_) {
    $typefaces{$typeface} = 1;
  }
  foreach $typeface (keys %parsed_typefaces) {
    return 0 if (!exists $typefaces{$typeface});
  }
  return 1;
}

sub format_versions(\%) {
  my ($versions_ref) = @_;
  
  my @ret = ();
  my %done_typefaces = ();
  foreach $version (sort keys %{$versions_ref}) {
    my ($str) = denormalize_version ($version);
    my $do_last = 1;
    if (@{$$versions_ref{$version}}) {
      my @print_typefaces = ();
      foreach $typeface (@{$$versions_ref{$version}}) {
        if (!exists ($done_typefaces{$typeface})) {
          $done_typefaces{$typeface} = 1;
          push (@print_typefaces, $typeface);
        }
      }
      next if (!@print_typefaces);
      if (!detect_full_typefaces_support(@print_typefaces)) {
        $str .= ' (' . join (', ', sort @print_typefaces) . ')';
        $do_last = 0;
      }
    }
    push (@ret, $str);
    last if ($do_last);
  }
  return join (' ', @ret);
}

sub print_status_file(\%) {
  my ($parsed_ref) = @_;
  
  print @{$$parsed_ref{'_'}};
  delete $$parsed_ref{'_'};
  foreach $hex_enc (sort {hex($a) <=> hex($b)} keys %{$parsed_ref}) {
    my ($versions) = format_versions (%{$$parsed_ref{$hex_enc}{'versions'}});
    printf ('U+%s %-'.$name_width.'s %s'."\n", $hex_enc, $$parsed_ref{$hex_enc}{'name'}, $versions);
  }
}

if (@ARGV < 3) {
  print STDERR "usage: version_tag status_file sfd_files+\n";
  exit 1;
}

$version_tag = shift @ARGV;
$status_file = shift @ARGV;
@sfd_files = @ARGV;

%parsed = ();

parse_status_file (%parsed, $status_file);
foreach $sfd_file (@sfd_files) {
  parse_sfd_file (%parsed, $version_tag, $sfd_file);
}

if ($debug) {
  print STDERR Data::Dumper->Dump([\%parsed], ['*parsed']);
  print STDERR "Parsed typefaces: ", join (', ', @parsed_typefaces), "\n";
}

print_status_file (%parsed);

1;
