SUBDIRS = src agent man

# .gz because github doesn't support .xz yet :-(

TAG		?= $(shell git log --pretty="format:%H" -n 1)
distdir		 = $(PACKAGE)-$(TAG)
TARFILE		 = $(distdir).tar.gz
DIST_ARCHIVES	 = $(TARFILE)

RPM_ROOT	= $(shell pwd)
RPM_OPTS	= --define "_sourcedir $(RPM_ROOT)" 	\
		  --define "_specdir   $(RPM_ROOT)" 	\
		  --define "_srcrpmdir $(RPM_ROOT)"

MOCK_TARGET     ?= rhel-7.1-candidate-x86_64
MOCK_OPTIONS	?= --resultdir=$(RPM_ROOT)/mock --no-cleanup-after

BUILD_COUNTER	?= build.counter
LAST_COUNT      = $(shell test ! -e $(BUILD_COUNTER) && echo 0; test -e $(BUILD_COUNTER) && cat $(BUILD_COUNTER))
COUNT           = $(shell expr 1 + $(LAST_COUNT))

export:
	rm -f $(PACKAGE)-HEAD.tar.*
	if [ -f $(TARFILE) ]; then						\
	    echo `date`: Using existing tarball: $(TARFILE);			\
	else									\
	    rm -f $(PACKAGE).tar.*;						\
	    git archive --prefix=$(distdir)/ $(TAG) | gzip > $(TARFILE);	\
	    echo `date`: Rebuilt $(TARFILE);					\
	fi

srpm:	export
	rm -f *.src.rpm
	sed -i 's/global\ commit.*/global\ commit\ $(TAG)/' $(PACKAGE).spec
	if [ -e $(BUILD_COUNTER) ]; then							\
		sed -i 's/global\ buildnum.*/global\ buildnum\ $(COUNT)/' $(PACKAGE).spec;	\
		echo $(COUNT) > $(BUILD_COUNTER);					\
	fi
	rpmbuild $(RPM_OPTS) -bs $(PACKAGE).spec

rpm:	export
	sed -i 's/global\ commit.*/global\ commit\ $(TAG)/' $(PACKAGE).spec
	rpmbuild $(RPM_OPTS) -ba $(PACKAGE).spec

mock:   srpm
	-rm -rf $(RPM_ROOT)/mock
	@echo "mock --root=$* --rebuild $(MOCK_OPTIONS) $(RPM_ROOT)/*.src.rpm"
	mock --root=$(MOCK_TARGET) --rebuild $(MOCK_OPTIONS) $(RPM_ROOT)/*.src.rpm

beekhof: mock
	cluster-helper -- 'rm -f sbd-*.x86_64.rpm'
	cluster-helper --copy $(RPM_ROOT)/mock/sbd-*.x86_64.rpm {}: 
	cluster-helper -- yum install -y sbd-*.x86_64.rpm
