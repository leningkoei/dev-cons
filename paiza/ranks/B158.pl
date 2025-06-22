# use POSIX qw(ceil);

my $len = <STDIN>;
chomp($len);
# my $mid = ceil ($len / 2);
my $mid = ($len + 1) / 2 - 1;

my @input_matrix = ();
for my $i (0..$len - 1) {
  my $row_string = <STDIN>;
  chomp($row_string);
  my @row = split(' ', $row_string);
  for my $j (0..$len - 1) {
    $input_matrix[$i][$j] = $row[$j];
  }
}

sub min ($$) {
  my ($x, $y) = @_;
  return $x > $y ? $y : $x;
}
sub max ($$) {
  my ($x, $y) = @_;
  return $x > $y ? $x : $y;
}

my @standard_matrix = ();
for my $i (0..$len - 1) {
  for my $j (0..$len - 1) {
    if ($i == 0 || $j == 0) {
      $standard_matrix[$i][$j] = 1;
    } elsif ($i <= $mid && $j <= $mid) {
      $standard_matrix[$i][$j] =
        min($standard_matrix[$i - 1][$j], $standard_matrix[$i][$j - 1]) + 1;
    } elsif ($i <= $mid && $j > $mid) {
      $standard_matrix[$i][$j] = $standard_matrix[$i][$mid * 2 - $j];
    } elsif ($i > $mid && $j <= $mid) {
      $standard_matrix[$i][$j] = $standard_matrix[$mid * 2 - $i][$j];
    } else {
      $standard_matrix[$i][$j] = $standard_matrix[$mid * 2 - $i][$mid * 2 - $j];
    }
  }
}

my $result = 0;
for my $i (0..$len - 1) {
  for my $j (0..$len - 1) {
    $result += max(0, $input_matrix[$i][$j] - $standard_matrix[$i][$j]);
  }
}

print $result . "\n";

# foreach my $row (@input_matrix) {
#   foreach my $number (@$row) {
#     print $number;
#     print " ";
#   }
#   print "\n";
# }
