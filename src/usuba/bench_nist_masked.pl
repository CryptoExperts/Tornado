#!/usr/bin/perl

use strict;
use warnings;
use v5.14;
$| = 1;
use Data::Printer;

use Getopt::Long;

my ($pattern, $order, $nb_run, $by_cipher, $by_slicing) = ("", 128, 5);
GetOptions("by-cipher"  => \$by_cipher,
           "by-slicing" => \$by_slicing,
           "pattern=s"  => \$pattern,
           "order=i"    => \$order,
           "nb-run=i"   => \$nb_run);

# Setting by_slicing by default
if (!$by_cipher && !$by_slicing) { $by_slicing = 1 }

my %times;
my $i = 0;
for (1 .. $nb_run) {
    say "###################  Run $_ #################";


    for my $code (glob("nist/*/usuba/bench/*{bit,v}slice.c")) {
        next if $code !~ /masked/; # ignoring masked implementations
        next if $pattern && $code !~ /$pattern/;

        print "\r\033[2KCompiling $code.....";
        system "clang -O3 -march=native -I arch -o _run experimentations/bench_generic/bench.c $code -D MASKING_ORDER=$order -D NB_RUN=10 -D WARMING=2 -D NUCLEO -fno-slp-vectorize -fno-vectorize";
        print " done.";

        print "\r\033[2KRunning $code.....";
        my ($cipher,$slicing) = $code =~ m{nist/([^/]+)/(?:.*_ua_((?:bit|v)slice))?};
        $slicing = 'ref' if $code =~ /ref\.c$/;
        my ($time) = `./_run` =~ /(\d+(?:\.\d+)?)/;
        $times{by_slicing}{$slicing}{$cipher} += $time / $nb_run;
        $times{by_cipher}{$cipher}{$slicing}  += $time / $nb_run;
        print " done.";

        unlink "_run";
    }
    print "\r\033[2K";

    if ($by_slicing) {
        for my $slicing (sort keys %{$times{by_slicing}}) {
            say "*************** $slicing ***************";
            for my $cipher (sort { $times{by_slicing}{$slicing}{$a} <=>
                                       $times{by_slicing}{$slicing}{$b} }
                            keys %{$times{by_slicing}{$slicing}}) {
                printf "%15s    %.2f\n", $cipher, $times{by_slicing}{$slicing}{$cipher};
            }
            say "";
        }
    }

    if ($by_cipher) {
        for my $cipher (sort keys %{$times{by_cipher}}) {
            say "##### $cipher";
            for my $slicing (sort keys %{$times{by_cipher}{$cipher}}) {
                printf "%9s    %.2f\n", $slicing, $times{by_cipher}{$cipher}{$slicing};
            }
            say "";
        }
    }

    say "\n\n#############################################\n\n";
}
