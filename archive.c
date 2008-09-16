#include "arch_object.h"
#include "runtime.h"

struct archive_s {
	struct archive_obj procs;
};

int arch_readable(archive_t archive){
	return (archive->procs.read!=NULL);
}
stream_t arch_read(archive_t archive,char *name){
	return archive->procs.read(archive,name);
}

int arch_writable(archive_t archive){
	return (archive->procs.write!=NULL);
}
stream_t arch_write(archive_t archive,char *name){
	return archive->procs.write(archive,name);
}

int arch_searchable(archive_t archive){
	return (archive->procs.list!=NULL);
}
void arch_search(archive_t archive,char *regex,string_enum_t cb,void*arg){
	archive->procs.list(archive,regex,cb,arg);
}

int arch_enumerable(archive_t archive){
	return (archive->procs.play!=NULL);
}
void arch_enum(archive_t archive,char *regex,struct archive_enum *cb,void*arg){
	archive->procs.play(archive,regex,cb,arg);
}

void arch_close(archive_t *archive){
	(*archive)->procs.close(archive);
}

struct cb_arg {
	int id;
	archive_t arch;
	struct archive_enum *cb;
	void *arg;
};

static void arch_copy(struct cb_arg *cba,char*name){
	cba->cb->new_item(cba->arg,cba->id,name);
	stream_t s=arch_read(cba->arch,name);
	char buf[4096];
	for(;;){
		int len=stream_read_max(s,buf,4096);
		if(len==0) break;
		cba->cb->data(cba->arg,cba->id,buf,len);
	}
	stream_close(&s);
	cba->cb->end_item(cba->arg,cba->id);
	cba->id++;
}

void arch_play(archive_t arch,char*regex,struct archive_enum *cb,void*arg){
	struct cb_arg cba;
	cba.id=0;
	cba.arch=arch;
	cba.cb=cb;
	cba.arg=arg;
	arch->procs.list(arch,regex,arch_copy,&cba);
}

